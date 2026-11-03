package bergdb.core;

import bergdb.dag.AccessData;
import bergdb.dag.Dag;
import bergdb.dag.GetData;
import bergdb.dag.KeyNode;
import bergdb.dag.Klong;
import bergdb.dag.Node;
import bergdb.dag.Spos;
import bergdb.dag.TopNode;
import bergdb.storage.MetaBlock;
import bergdb.storage.RecoverableStream;
import bergdb.stream.MemoryStream;

/**
 * Probe for review R1 (016-06), doubt D1 of R1-F1's race: a reader's follow of a pointer to a
 * key node while the writer appends to the predecessor and its arrays grow
 * (KeyNode.growCapacity). The slow path reads the pair under the predecessor's monitor and
 * then NodeCollection.pointsToIndexNode reads klongs[i] again; a klong 0 from a new array
 * makes it follow the pointer as a pointer to a value. The writer makes fresh inner key
 * nodes: time 10, key 1 with a stream pointer to a key node at 1000 (id 1001), published,
 * then keys 2..61 (growths at 2, 6, 14, 30). The reader follows pointer 1 of each new node
 * once. Usage (before the jar): java -cp probes:build/bergdb.jar bergdb.core.GrowFollowProbe SECONDS
 */
public class GrowFollowProbe {
    static volatile KeyNode cur;
    static volatile boolean stop;

    static class Stream extends NodeStream {
        final KeyNode child;
        Stream(KeyNode child) {
            super(new RecoverableStream(new MemoryStream(), new MetaBlock()), new Object());
            this.child = child;
        }
        public NodeHeader readNodeHeader(long pos) {
            return new NodeHeader(Node.TYPE_KEY_NODE, child.getId());
        }
        public Node readNode(long pos) {
            KeyNode k = new KeyNode(true);
            k.addToEnd(Klong.createTime(10), null, Spos.NULL);
            k.addToEnd(Klong.createKey(new byte[] {9}), null, 5000);
            k.setId(child.getId());
            k.setSpos(pos);
            return k;
        }
    }

    public static void main(String[] args) throws Exception {
        final long seconds = Long.parseLong(args.length > 0 ? args[0] : "20");
        final long[] keys = new long[62];
        for (int i = 1; i < 62; i++) keys[i] = Klong.createKey(new byte[] {(byte) i});
        KeyNode child = new KeyNode(true);
        child.setId(1001);
        child.setSpos(1000);
        final NodeCollection nc = new NodeCollection(new Cache.DbInfo() {}, new Stream(child));
        final GetData op = new GetData();
        op.accessData = AccessData.DEFAULT_ACCESS_DATA;
        op.cachePolicy = Dag.CACHE_ALL;
        op.pointerListener = new Dag.PointerListener() {
            public void superRootAccessed(TopNode superRoot) {}
            public void pointerFollowed(Node pred, int index, Node result, int type) {}
        };
        Thread writer = new Thread(new Runnable() {
            public void run() {
                long id = 3;
                while (!stop) {
                    KeyNode k = new KeyNode(false);
                    k.addToEnd(Klong.createTime(10), null, Spos.NULL);
                    k.addToEnd(keys[1], null, 1000);
                    k.setId(id += 2);
                    cur = k;
                    for (int i = 2; i < 62; i++) k.addToEnd(keys[i], null, 1000);
                }
            }
        });
        final long[] seen = new long[4];
        final String[] first = new String[1];
        Thread reader = new Thread(new Runnable() {
            public void run() {
                long follows = 0, notKeyNode = 0, thrown = 0;
                KeyNode last = null;
                while (!stop) {
                    KeyNode k = cur;
                    if (k == null || k == last) continue;
                    last = k;
                    try {
                        Node n = nc.followPointer(k, 1, op);
                        if (!(n instanceof KeyNode)) notKeyNode++;
                    } catch (Throwable e) {
                        thrown++;
                        if (first[0] == null) first[0] = e.toString();
                    }
                    follows++;
                }
                seen[0] = follows; seen[1] = notKeyNode; seen[2] = thrown;
            }
        });
        writer.start();
        reader.start();
        Thread.sleep(seconds * 1000);
        stop = true;
        writer.join();
        reader.join();
        System.out.println("follows " + seen[0] + ", not a key node: " + seen[1] + ", thrown: "
                + seen[2] + (first[0] == null ? "" : ", the first: " + first[0]));
    }
}
