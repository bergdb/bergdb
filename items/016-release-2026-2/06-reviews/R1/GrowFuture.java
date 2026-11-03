import bergdb.dag.KeyNode;
import bergdb.dag.Klong;
import bergdb.dag.KlongWithPointer;
import bergdb.dag.Spos;

/**
 * Probe for review R1 (016-06), the second effect of R1-F1: a search that does not see the
 * copy of a time klong after a growth (KeyNode.growCapacity) goes on past it, into klongs of
 * a later time. The writer fills fresh leaves: time 10, key 1 with reference 1008; time 20
 * (a later transaction), key 1 again with reference 2008, and keys 2..57 at time 20, so that
 * the arrays grow at 6, 14 and 30 klongs. The reader searches key 1 at time 15, whose answer
 * is the klong of time 10 (reference 1008), in every leaf of size 4 or more; 2008 is a value
 * from after the lookup time. Usage: java -cp build/bergdb.jar:. GrowFuture SECONDS
 */
public class GrowFuture {
    static volatile KeyNode cur;
    static volatile boolean stop;

    public static void main(String[] args) throws Exception {
        final long seconds = Long.parseLong(args.length > 0 ? args[0] : "20");
        final long[] keys = new long[62];
        for (int i = 1; i < 62; i++) keys[i] = Klong.createKey(new byte[] {(byte) i});
        final long cv1 = Klong.getCompareValue(keys[1]);
        Thread writer = new Thread(new Runnable() {
            public void run() {
                while (!stop) {
                    KeyNode k = KeyNode.nodeWithTime(10);
                    k.addToEnd(keys[1], null, 1008);
                    cur = k;
                    k.addToEnd(Klong.createTime(20), null, Spos.NULL);
                    k.addToEnd(keys[1], null, 2008);
                    for (int i = 2; i < 58; i++) k.addToEnd(keys[i], null, 1000 + 8 * i);
                }
            }
        });
        final long[] seen = new long[4];
        Thread reader = new Thread(new Runnable() {
            public void run() {
                KlongWithPointer kwi = new KlongWithPointer();
                long searches = 0, future = 0, misses = 0, other = 0;
                while (!stop) {
                    KeyNode k = cur;
                    if (k == null || k.size < 4) continue;
                    k.searchEq(15, cv1, kwi);
                    searches++;
                    if (kwi.klong == Klong.NULL) misses++;
                    else if (kwi.pos == 2008) future++;
                    else if (kwi.pos != 1008) other++;
                }
                seen[0] = searches; seen[1] = future; seen[2] = misses; seen[3] = other;
            }
        });
        writer.start();
        reader.start();
        Thread.sleep(seconds * 1000);
        stop = true;
        writer.join();
        reader.join();
        System.out.println("searches " + seen[0] + ", the value of time 20 at time 15: " + seen[1]
                + ", key 1 not found: " + seen[2] + ", another reference: " + seen[3]);
    }
}
