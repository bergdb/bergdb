package bergdb.core;

import java.util.Map;

/**
 * Times NodeCollection.forgetIdsBelow on a full idByPos (100,000 entries), keeping all,
 * about 30 %, about 20 % (a copy to a new map) and none; bergdb 026-10, section 4.
 * Usage, from java/ after build.sh (the probe before the jar on the class path):
 *   javac -d DIR -cp build/classes ForgetProbe.java
 *   java -cp DIR:build/bergdb.jar bergdb.core.ForgetProbe
 */
public class ForgetProbe {
    @SuppressWarnings("unchecked")
    public static void main(String[] args) throws Exception {
        bergdb.storage.RecoverableStream rs = new bergdb.storage.RecoverableStream(
                new bergdb.stream.MemoryStream(), new bergdb.storage.MetaBlock());
        NodeCollection c = new NodeCollection(new Cache.DbInfo() {}, new NodeStream(rs, new Object()));
        java.lang.reflect.Field f = NodeCollection.class.getDeclaredField("idByPos");
        f.setAccessible(true);
        java.lang.reflect.Field lf = NodeCollection.class.getDeclaredField("idLock");
        lf.setAccessible(true);
        java.util.Random rnd = new java.util.Random(1);
        for (int round = 0; round < 16; round++) {
            Map<Long, Long> m = (Map<Long, Long>) f.get(c);
            synchronized (lf.get(c)) {
                for (int i = 0; i < 100000; i++) {
                    long pos = 1000000000L + rnd.nextInt(1 << 30);
                    m.put(pos, pos + 7);
                }
                for (int i = 0; i < 100000; i++) m.get(1000000000L + rnd.nextInt(1 << 30));
            }
            int before = m.size();
            // keep all; keep about 30 %; keep about 20 % (a copy); keep none
            long below = round % 4 == 0 ? 0 : round % 4 == 1 ? 1000000000L + (long) (0.7 * (1 << 30))
                    : round % 4 == 2 ? 1000000000L + (long) (0.8 * (1 << 30)) : Long.MAX_VALUE;
            long t0 = System.nanoTime();
            c.forgetIdsBelow(below);
            long t = System.nanoTime() - t0;
            System.out.printf("round %d: %d entries, kept %d, %.2f ms%n", round, before,
                    ((Map<Long, Long>) f.get(c)).size(), t / 1e6);
        }
    }
}
