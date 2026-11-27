package bergdb.core;

/** 031-07 probe: the records near position 512 of two originals of one workload. */
public class StaleLook {
    public static void main(String[] args) {
        long seed = 20768;
        for (CorruptStreamTester.Config cfg : new CorruptStreamTester.Config[] {
                CorruptStreamTester.ALL, CorruptStreamTester.LONG}) {
            CorruptStreamTester.Original a = CorruptStreamTester.write(cfg, seed * 31 + cfg.name.hashCode());
            CorruptStreamTester.Original b = CorruptStreamTester.write(cfg, seed * 31 + cfg.name.hashCode() + 7777);
            for (CorruptStreamTester.Original o : new CorruptStreamTester.Original[] {a, b}) {
                StringBuilder s = new StringBuilder(cfg.name + ":");
                for (CorruptStreamTester.Record r : o.records) {
                    if (r.tpos > 1200) break;
                    s.append(" [" + r.tpos + ", size " + r.size + ", tt " + bergdb.common.Bytes.bytesToLongLE(r.bytes, 8) + "]");
                }
                System.out.println(s);
            }
        }
    }
}
