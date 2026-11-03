import bergdb.dag.Handle;
import bergdb.dag.KeyNode;
import bergdb.dag.Klong;
import bergdb.dag.Pointee;

/**
 * Probe for review R1 (016-06): KeyNode.growCapacity replaces the arrays klongs, pointers
 * and pos with copies, plainly, while readers that read 'size' before the growth read the
 * fields without an edge to the copies (KeyNode's class comment: "Existing data in them does
 * not change"). A reader that sees a new array with default contents below 'size' reads a
 * klong 0 (a time klong of time 0), a null pointer, or a reference 0.
 *
 * The writer fills fresh key nodes to 62 klongs (growths at 2, 6, 14, 30); the reader reads
 * size (volatile) and then each array, as KeyNode's searches and followPointer do, and counts
 * elements below size with their default value. Usage: java -cp build/bergdb.jar:. GrowRace SECONDS
 */
public class GrowRace {
    static volatile KeyNode cur;
    static volatile boolean stop;

    public static void main(String[] args) throws Exception {
        final long seconds = Long.parseLong(args.length > 0 ? args[0] : "20");
        final Handle h = new Handle(7);
        final long key = Klong.createKey(new byte[] {1});
        Thread writer = new Thread(new Runnable() {
            public void run() {
                long rounds = 0;
                while (!stop) {
                    KeyNode k = new KeyNode(false);
                    cur = k;
                    for (int i = 0; i < 62; i++) k.addToEnd(key, h, 1000 + 8 * i);
                    rounds++;
                }
                System.out.println("writer rounds: " + rounds);
            }
        });
        final long[] seen = new long[4];
        Thread reader = new Thread(new Runnable() {
            public void run() {
                long reads = 0, zeroKlong = 0, nullPointer = 0, zeroPos = 0;
                while (!stop) {
                    KeyNode k = cur;
                    if (k == null) continue;
                    int s = k.size;                 // volatile, as the searches
                    long[] kl = k.klongs;           // plain, as the searches
                    Pointee[] p = k.pointers;       // plain, as getPointee
                    long[] ps = k.pos;              // plain, as getPointerPos
                    if (s == 0) continue;
                    int j = s - 1;
                    if (j < kl.length && kl[j] == 0) zeroKlong++;
                    if (j < p.length && p[j] == null) nullPointer++;
                    if (j < ps.length && ps[j] == 0) zeroPos++;
                    if (kl[0] == 0) zeroKlong++;
                    reads++;
                }
                seen[0] = reads; seen[1] = zeroKlong; seen[2] = nullPointer; seen[3] = zeroPos;
            }
        });
        writer.start();
        reader.start();
        Thread.sleep(seconds * 1000);
        stop = true;
        writer.join();
        reader.join();
        System.out.println("reads " + seen[0] + ", klong 0 below size: " + seen[1]
                + ", null pointer below size: " + seen[2] + ", reference 0 below size: " + seen[3]);
    }
}
