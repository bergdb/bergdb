package bergdb.core;

import java.io.IOException;
import java.io.UnsupportedEncodingException;
import java.util.ArrayList;

import bergdb.common.Bytes;
import bergdb.common.StringUtil;
import bergdb.dag.KeyNode;
import bergdb.dag.Keys;
import bergdb.dag.Node;
import bergdb.dag.TopNode;
import bergdb.dag.ValueNode;
import bergdb.nanotest.Assert;
import bergdb.nanotest.Nano;
import bergdb.pub.util.DatabaseNotCreatedException;
import bergdb.pub.util.SyncLevel;
import bergdb.storage.MetaBlock;
import bergdb.storage.RecoverableStream;
import bergdb.storage.StreamFormatException;
import bergdb.stream.AppendOnlyStream;
import bergdb.stream.MemoryStream;

/**
 * Class with nanotests for NodeStream.
 * 
 * @author Frans Lundberg
 */
public class NodeStreamTester {
    
    @Nano
    public static void testSimpleRestart() {
        MemoryStream mstream = new MemoryStream();
        CoreTestClock clock = new CoreTestClock();
        Db db = Db.builder().testSetup().mainStream(mstream).startupDistance(10000).clock(clock).build();
        db.start();
        clock.setTime(10);
        db.execute(db.trans().put("admin1", "Sanna").build());

        byte[] value;
        value = DbUtil.get(db, 99, "admin1");
        Assert.assertArrayEquals(StringUtil.toBytes("Sanna"), value);
        db.sync(SyncLevel.ORDINARY);
        db.close();
        
        Db db2 = Db.builder().testSetup().mainStream(mstream.copy()).build();
        db2.start();
        
        value = DbUtil.get(db2, 99, "admin1");
        Assert.assertArrayEquals(StringUtil.toBytes("Sanna"), value);
        
        value = DbUtil.get(db2, 5, "admin1");
        Assert.assertNull(value);
        db2.close();
    }
    
    @Nano
    public static void testSimpleRestart2() {
        //
        // Like testSimpleRestart, but 2-segment key
        //
        byte[] value;
        MemoryStream mstream = new MemoryStream();
        CoreTestClock clock = new CoreTestClock();
        Db db = Db.builder().testSetup().mainStream(mstream).clock(clock).build();
        db.start();
        clock.setTime(10);
        db.execute(db.trans().put("admin10", "Sanna").build());
        
        value = DbUtil.get(db, 99, "admin10");
        Assert.assertArrayEquals(StringUtil.toBytes("Sanna"), value);
        db.sync(SyncLevel.ORDINARY);
        db.close();
        
        Db db2 = Db.builder().testSetup().mainStream(mstream.copy()).build();
        db2.start();
        
        value = DbUtil.get(db2, 99, "admin10");
        Assert.assertArrayEquals(StringUtil.toBytes("Sanna"), value);
        
        value = DbUtil.get(db2, 5, "admin10");
        Assert.assertNull(value);
        db2.close();
    }
    
    @Nano
    public static void testRestartWithMultipleTransactions() {
        MemoryStream s = new MemoryStream();
        CoreTestClock clock = new CoreTestClock();
        Db db = Db.builder().testSetup().mainStream(s).clock(clock).build();
        db.start();
        clock.setTime(10);
        db.execute(db.trans().put("admin1", "Sanna1").build());
        clock.setTime(20);
        db.execute(db.trans().put("admin2", "Sanna2").build());
        db.sync(SyncLevel.ORDINARY);
        db.close();
        
        Db db2 = Db.builder().testSetup().mainStream(s.copy()).build();
        db2.start();
        byte[] value;
        
        value = DbUtil.get(db2, 99, "admin1");
        Assert.assertArrayEquals(StringUtil.toBytes("Sanna1"), value);
        value = DbUtil.get(db2, 5, "admin1");
        Assert.assertNull(value);
        
        value = DbUtil.get(db2, 99, "admin2");
        Assert.assertArrayEquals(StringUtil.toBytes("Sanna2"), value);
        value = DbUtil.get(db2, 15, "admin2");
        Assert.assertNull(value);
        db2.close();
    }
    
    @Nano
    private static void tIterators1() throws UnsupportedEncodingException {
        AppendOnlyStream s = new MemoryStream();
        Db db = Db.builder().testSetup().mainStream(s).build();
        db.start();
        db.execute(db.trans().put("admin1", "a1").put("admin2", "a2"));
        db.execute(db.trans().put("admin3", "a3"));
        db.execute(db.trans().put("admin4", "a4"));
        
        NodeStream.TransIterator ti = db.internal().nodeStream().createTransIterator(0);
        ti.next();
        ti.next();
        StoredTrans stored = ti.getStoredTrans();
        
        Assert.assertEquals(2, stored.nodes.length);
        Assert.assertTrue(stored.nodes[0] instanceof StoredValueNode);
        StoredValueNode storedValue = (StoredValueNode) stored.nodes[0];
        Assert.assertEquals("a1", new String(storedValue.getNode().getValue(), "UTF-8"));
        db.close();
    }
    
    private static NodeStream createTestNodeStream() {
        AppendOnlyStream stream = new MemoryStream();
        MetaBlock metaBlock = new MetaBlock();
        RecoverableStream rstream = new RecoverableStream(stream, metaBlock);
        NodeStream nodeStream = new NodeStream(rstream, new Object());
        return nodeStream;
    }
    
    @Nano
    private static void testReadNodeHeader1() {
        // Tests reading a TopNode header.
        
        NodeStream nodeStream = createTestNodeStream();
        TransNodes transNodes = new TransNodes();
        Trans trans = new Trans.Builder().build();
        
        TopNode n1 = TopNode.createDummy(5);
        n1.setId(12L);
        transNodes.addTopNode(n1);
        
        nodeStream.appendNodes(transNodes, trans, new ArrayList<Node>());
        Assert.assertTrue(n1.getSpos() > 0);
        
        NodeHeader header1 = nodeStream.readNodeHeader(n1.getSpos());
        Assert.assertEquals(Node.TYPE_TOP_NODE, header1.type());
        Assert.assertEquals("id", 12L, header1.id());
    }
    
    @Nano
    private static void testReadNodeHeader2() {
        // Tests reading a KeyNode header.
        
        NodeStream nodeStream = createTestNodeStream();
        TransNodes transNodes = new TransNodes();
        Trans trans = new Trans.Builder().build();
        
        KeyNode node = new KeyNode();
        node.setId(13L);
        transNodes.addKeyNode(node);
        
        nodeStream.appendNodes(transNodes, trans, new ArrayList<Node>());
        Assert.assertTrue(node.getSpos() > 0);
        
        NodeHeader header = nodeStream.readNodeHeader(node.getSpos());
        Assert.assertEquals("type", Node.TYPE_KEY_NODE, header.type());
        Assert.assertEquals(13L, header.id());
    }
    
    @Nano
    private static void testReadNodeHeader3() {
        // Tests reading a ValueNode header.
        
        NodeStream nodeStream = createTestNodeStream();
        TransNodes transNodes = new TransNodes();
        Trans trans = new Trans.Builder().build();
        
        ValueNode node = new ValueNode(new byte[1]);
        node.setId(1234L);
        transNodes.addValueNode(node, Keys.toSegments("/-ddir"));
        
        nodeStream.appendNodes(transNodes, trans, new ArrayList<Node>());
        Assert.assertTrue(node.getSpos() > 0);
        
        NodeHeader header = nodeStream.readNodeHeader(node.getSpos());
        Assert.assertEquals("type", Node.TYPE_VALUE, header.type());
        Assert.assertEquals(node.getId(), header.id());
        Assert.assertEquals(1234L, node.getId());
    }

    /**
     * Bergdb 005-28: a failed transaction where an iterator starts (its last byte is 0, as
     * recovery's zero fill leaves a torn one). Both iterators went back to it, for ever. Now
     * the iterator from an exact start pos throws, as a start pos must name a committed
     * transaction, and the iterator from the last transaction completed before a position
     * steps on to the next transaction.
     */
    @Nano
    public static void testTransIteratorAtFailedTrans() throws InterruptedException {
        MemoryStream stream = new MemoryStream();
        Object writeLock = new Object();
        final NodeStream nodeStream = new NodeStream(
                new RecoverableStream(stream, new MetaBlock()), writeLock);
        final Trans t1 = appendTopNode(nodeStream);
        stream.truncate(t1.lastPos);        // A crash before t1's last byte,
        synchronized (writeLock) {
            nodeStream.recover();           // and recovery zero-fills t1.
        }
        Trans t2 = appendTopNode(nodeStream);
        Assert.assertEquals(t1.nextPos, t2.tpos);
        
        Throwable e = thrownWithin10s(new Runnable() {
            public void run() {
                nodeStream.createTransIteratorFromExactStartupPos(t1.tpos).next();
            }
        });
        Assert.assertTrue("thrown: " + e, e instanceof StreamFormatException);
        Assert.assertTrue(e.getMessage(), e.getMessage().contains(" " + t1.tpos + " "));
        
        // The first meta block names no transaction, so this one starts at t1.
        final NodeStream.TransIterator ti = nodeStream.createTransIterator(0);
        final boolean[] next = new boolean[1];
        e = thrownWithin10s(new Runnable() {
            public void run() {
                next[0] = ti.next();
            }
        });
        Assert.assertTrue("thrown: " + e, e == null && next[0]);
        Assert.assertEquals("the transaction after t1", t2.tpos, ti.tpos);
        Assert.assertFalse(ti.next());
    }
    
    /**
     * Bergdb 005-28, as 005-11's probe P9 found it: the transaction at the startup pos is a
     * failed one, in a stream that mixes two histories. The main's recovery zero-filled x,
     * which a replica holds whole, and the replica's next transaction t, copied after it, names
     * x as its startup pos. Startup looped for ever on x; now it throws.
     */
    @Nano
    public static void testStartupPosAtFailedTrans() throws IOException, InterruptedException {
        MemoryStream s = new MemoryStream();
        Db db = Db.builder().testSetup(s).startupDistance(10).start();
        Trans x = null;
        Trans t = null;
        for (int i = 0; i < 4; i++) {
            x = t;
            t = db.trans().put("/k" + i, "v" + i).build();
            db.execute(t);
        }
        db.close();
        Assert.assertEquals("t's startup pos", x.tpos, t.startupPos);
        Assert.assertEquals("t follows x", x.nextPos, t.tpos);
        
        // x as recovery leaves it after a crash before its last byte.
        MemoryStream mixed = s.copy();      // close() closed s.
        MemoryStream.TestAccess.write(mixed, new byte[] {0}, x.lastPos);
        Throwable e = startWithin10s(mixed);
        Assert.assertTrue("thrown: " + e, e instanceof StreamFormatException);
        Assert.assertTrue(e.getMessage(), e.getMessage().contains(" " + x.tpos + " "));
    }
    
    /**
     * Bergdb 005-28 in one history: a crash while the database is created, in its first
     * transaction (the primordial one). Recovery zero-fills it, and startup, which starts
     * there as the meta block names no transaction, looped for ever. Now it throws. Since
     * 2026-10-25 (005-33) the start refuses such a stream before recovery, with a
     * DatabaseNotCreatedException, and writes nothing; DbTester.testCrash8InCreation has every
     * cut.
     */
    @Nano
    public static void testCrashInPrimordialTrans() throws IOException, InterruptedException {
        MemoryStream s = new MemoryStream();
        Db.builder().testSetup(s).start().close();
        MemoryStream created = s.copy();    // close() closed s.
        final long first = RecoverableStream.META_BLOCK_SIZE;
        final long end = created.getLength();
        byte[] size = new byte[4];
        created.read(first, size, 0, 4);
        Assert.assertEquals("one transaction", end - first, Bytes.bytesToIntLE(size, 0));
        
        // Cuts after 1, 4 and 5 of its bytes, in the middle and before its last byte.
        for (long cut : new long[] {first + 1, first + 4, first + 5, (first + end) / 2, end - 1}) {
            MemoryStream m = created.copy();
            m.truncate(cut);
            Throwable e = startWithin10s(m);
            Assert.assertTrue("cut at " + cut + ", thrown: " + e,
                    e instanceof DatabaseNotCreatedException);
            Assert.assertEquals("cut at " + cut + ", unchanged", cut, m.getLength());
        }
    }
    
    private static Trans appendTopNode(NodeStream nodeStream) {
        TransNodes transNodes = new TransNodes();
        TopNode top = TopNode.createDummy(5);
        top.setId(12L);
        transNodes.addTopNode(top);
        Trans trans = new Trans.Builder().build();
        nodeStream.appendNodes(transNodes, trans, new ArrayList<Node>());
        return trans;
    }
    
    /** Starts a database on the stream; returns what start() threw, or null. */
    private static Throwable startWithin10s(AppendOnlyStream stream) throws InterruptedException {
        final Db db = Db.builder().testSetup(stream).build();
        Throwable e = thrownWithin10s(new Runnable() {
            public void run() {
                db.start();
            }
        });
        db.stop();
        return e;
    }
    
    /**
     * Runs r in a daemon thread; returns what it threw, or null. Fails if r has not returned
     * within 10 s: before bergdb 005-28, it could loop for ever.
     */
    private static Throwable thrownWithin10s(final Runnable r) throws InterruptedException {
        final Throwable[] thrown = new Throwable[1];
        Thread t = new Thread(new Runnable() {
            public void run() {
                try {
                    r.run();
                } catch (Throwable e) {
                    thrown[0] = e;
                }
            }
        });
        t.setDaemon(true);
        t.start();
        t.join(10 * 1000);
        Assert.assertFalse("still running after 10 s", t.isAlive());
        return thrown[0];
    }
}
