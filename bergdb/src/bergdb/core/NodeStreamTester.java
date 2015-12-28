package bergdb.core;

import java.io.UnsupportedEncodingException;
import java.util.ArrayList;

import bergdb.common.Util;
import bergdb.dag.KeyNode;
import bergdb.dag.Keys;
import bergdb.dag.Node;
import bergdb.dag.TopNode;
import bergdb.dag.ValueNode;
import bergdb.nanotest.Assert;
import bergdb.nanotest.Nano;
import bergdb.storage.MetaBlock;
import bergdb.storage.RecoverableStream;
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
        AppendOnlyStream mstream = new MemoryStream();
        CoreTestClock clock = new CoreTestClock();
        Db db = Db.builder().testSetup().mainStream(mstream).startupDistance(10000).clock(clock).build();
        db.start();
        clock.setTime(10);
        db.execute(db.trans().put("admin1", "Sanna").build());

        byte[] value;
        value = DbUtil.get(db, 99, "admin1");
        Assert.assertArrayEquals(Util.toBytes("Sanna"), value);
        db.sync(SyncLevel.ORDINARY);
        db = null;
        
        Db db2 = Db.builder().testSetup().mainStream(mstream).build();
        db2.start();
        
        value = DbUtil.get(db2, 99, "admin1");
        Assert.assertArrayEquals(Util.toBytes("Sanna"), value);
        
        value = DbUtil.get(db2, 5, "admin1");
        Assert.assertNull(value);
    }
    
    @Nano
    public static void testSimpleRestart2() {
        //
        // Like testSimpleRestart, but 2-segment key
        //
        byte[] value;
        AppendOnlyStream mstream = new MemoryStream();
        CoreTestClock clock = new CoreTestClock();
        Db db = Db.builder().testSetup().mainStream(mstream).clock(clock).build();
        db.start();
        clock.setTime(10);
        db.execute(db.trans().put("admin10", "Sanna").build());
        
        value = DbUtil.get(db, 99, "admin10");
        Assert.assertArrayEquals(Util.toBytes("Sanna"), value);
        db.sync(SyncLevel.ORDINARY);
        db = null;
        
        Db db2 = Db.builder().testSetup().mainStream(mstream).build();
        db2.start();
        
        value = DbUtil.get(db2, 99, "admin10");
        Assert.assertArrayEquals(Util.toBytes("Sanna"), value);
        
        value = DbUtil.get(db2, 5, "admin10");
        Assert.assertNull(value);
    }
    
    @Nano
    public static void testRestartWithMultipleTransactions() {
        AppendOnlyStream s = new MemoryStream();
        CoreTestClock clock = new CoreTestClock();
        Db db = Db.builder().testSetup().mainStream(s).clock(clock).build();
        db.start();
        clock.setTime(10);
        db.execute(db.trans().put("admin1", "Sanna1").build());
        clock.setTime(20);
        db.execute(db.trans().put("admin2", "Sanna2").build());
        db.sync(SyncLevel.ORDINARY);
        db = null;
        
        Db db2 = Db.builder().testSetup().mainStream(s).build();
        db2.start();
        byte[] value;
        
        value = DbUtil.get(db2, 99, "admin1");
        Assert.assertArrayEquals(Util.toBytes("Sanna1"), value);
        value = DbUtil.get(db2, 5, "admin1");
        Assert.assertNull(value);
        
        value = DbUtil.get(db2, 99, "admin2");
        Assert.assertArrayEquals(Util.toBytes("Sanna2"), value);
        value = DbUtil.get(db2, 15, "admin2");
        Assert.assertNull(value);
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
        transNodes.addIndexNode(n1);
        
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
        transNodes.addIndexNode(node);
        
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
        transNodes.addValueNode(node, Keys.toSegments("/-ddir"));
        
        nodeStream.appendNodes(transNodes, trans, new ArrayList<Node>());
        Assert.assertTrue(node.getSpos() > 0);
        
        NodeHeader header = nodeStream.readNodeHeader(node.getSpos());
        Assert.assertEquals("type", Node.TYPE_VALUE, header.type());
        Assert.assertEquals(node.getSpos(), header.id());
    }
}
