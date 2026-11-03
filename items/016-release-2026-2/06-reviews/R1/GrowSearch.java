import bergdb.dag.KeyNode;
import bergdb.dag.Klong;
import bergdb.dag.KlongWithPointer;
import bergdb.dag.Spos;

/**
 * Probe for review R1 (016-06): a reader's KeyNode.searchEq misses a key that the node has
 * had since before the reader's search, while the writer appends to the node and its arrays
 * grow (KeyNode.growCapacity). The writer fills fresh leaves: a time klong (time 10), then
 * keys 1..61, each with a stream pointer to position 1000 + 8 i; the growths come at 2, 6,
 * 14 and 30 klongs. The reader takes the current leaf, reads its size, and if key 1 is
 * there (size at least 2), searches for it at time 10, as a get does; a miss, or a hit with
 * a reference other than 1008, is a wrong answer. Usage: java -cp build/bergdb.jar:. GrowSearch SECONDS
 */
public class GrowSearch {
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
                    cur = k;
                    for (int i = 1; i < 62; i++) k.addToEnd(keys[i], null, 1000 + 8 * i);
                }
            }
        });
        final long[] seen = new long[4];
        Thread reader = new Thread(new Runnable() {
            public void run() {
                KlongWithPointer kwi = new KlongWithPointer();
                long searches = 0, misses = 0, badRef = 0;
                while (!stop) {
                    KeyNode k = cur;
                    if (k == null || k.size < 2) continue;
                    k.searchEq(10, cv1, kwi);
                    searches++;
                    if (kwi.klong == Klong.NULL) misses++;
                    else if (kwi.pos != 1008) badRef++;
                }
                seen[0] = searches; seen[1] = misses; seen[2] = badRef;
            }
        });
        writer.start();
        reader.start();
        Thread.sleep(seconds * 1000);
        stop = true;
        writer.join();
        reader.join();
        System.out.println("searches " + seen[0] + ", key 1 not found: " + seen[1]
                + ", found with a wrong reference: " + seen[2]);
    }
}
