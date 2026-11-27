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
import bergdb.storage.StreamIoException;
import bergdb.stream.AppendOnlyStream;
import bergdb.stream.MemoryStream;
import bergdb.stream.ReadBelowFirstPosException;

/**
 * Class with nanotests for NodeStream.
 * 
 * @author Frans Lundberg
 */
public class NodeStreamTester {

    /** bergdb 005-74, F3: refuse corrupt sizes before allocating their buffers. */
    @Nano
    private static void testCorruptReadNodeSize() throws IOException {
        checkCorruptReadSize(0);
    }

    @Nano
    private static void testCorruptReadTransSize() throws IOException {
        checkCorruptReadSize(1);
    }

    @Nano
    private static void testCorruptIteratorSize() throws IOException {
        checkCorruptReadSize(2);
    }

    /**
     * QL7 (bergdb 024-17, 6.5; 024-24): the reader reads a record's size and format byte
     * first. A size over the record limit (L7) is corrupt, also where the stream would hold
     * it; a committed record of another format, older or newer, is refused with
     * VersioningStreamException by both readers, and an uncommitted one (last byte 0) is
     * skipped by the iterator as before.
     */
    @Nano
    private static void testRecordHeaderFirst() throws IOException {
        byte[] bytes = new byte[132];
        Bytes.intToBytesLE(Integer.MAX_VALUE - 7, bytes, 128);
        MemoryStream big = new MemoryStream();
        big.append(bytes, 0, bytes.length);
        NodeStream ns = new NodeStream(new RecoverableStream(big, new MetaBlock()), new Object());
        try {
            ns.readTransBytes(128);
            throw new AssertionError("a size over L7 was read");
        } catch (StreamFormatException e) {
            Assert.assertTrue(e.getMessage(), e.getMessage().contains("(bergdb 024-17, L7)"));
        }
        for (int format : new int[] {6, StoredTrans.RECORD_FORMAT + 1}) {
            for (int reader = 0; reader < 2; reader++) {
                int size = 1000;
                byte[] record = new byte[128 + size];
                Bytes.intToBytesLE(size, record, 128);
                record[128 + 4] = (byte) format;
                record[128 + size - 1] = RecoverableStream.LAST_BYTE;
                MemoryStream stream = new MemoryStream();
                stream.append(record, 0, record.length);
                NodeStream n = new NodeStream(new RecoverableStream(stream, new MetaBlock()),
                        new Object());
                try {
                    if (reader == 0) {
                        n.readTransBytes(128);
                    } else {
                        n.createTransIteratorFromExactStartupPos(128).next();
                    }
                    throw new AssertionError("format " + format + " was read");
                } catch (bergdb.storage.VersioningStreamException e) {
                    Assert.assertTrue(e.getMessage(), e.getMessage().contains("format version "
                            + format + ";"));
                }
            }
        }
    }

    /**
     * bergdb 031-06 (Frans, 2026-11-27, 14:36): release 2026.7 does not open a database of
     * release 2026.6, whose records are of format 8. A start on a stream whose records are
     * of format 8, here this build's database with each record's format byte set to 8, is
     * refused with a VersioningStreamException that names release 2026.6, and nothing is
     * appended to the stream.
     */
    @Nano
    private static void testStartRefusesFormat8() throws IOException {
        final MemoryStream s = new MemoryStream();
        final CoreTestClock clock = new CoreTestClock();
        clock.setTime(1000 * 1000);
        try (Db db = Db.builder().testSetup(s).clock(clock).start()) {
            for (int i = 0; i < 20; i++) {
                clock.setTime(1000 * 1000 + 1000 * (i + 1));
                db.execute(db.trans().put("/k" + i, "v" + i).build());
            }
        }
        final byte[] bytes = new byte[(int) s.getLength()];
        s.read(0, bytes, 0, bytes.length);
        int records = 0;
        for (long pos = RecoverableStream.META_BLOCK_SIZE; pos < bytes.length; ) {
            final int size = Bytes.bytesToIntLE(bytes, (int) pos);
            final int f = (int) RecoverableStream.getSpos(pos, 4);
            Assert.assertEquals(StoredTrans.RECORD_FORMAT, bytes[f]);
            bytes[f] = 8;
            records++;
            pos = RecoverableStream.getSpos(pos, size);
        }
        Assert.assertTrue("records " + records, records > 20);
        final MemoryStream old = new MemoryStream();
        old.append(bytes, 0, bytes.length);
        Throwable refusal = null;
        try {
            Db.builder().testSetup(old).clock(clock).start().close();
        } catch (Exception e) {
            refusal = e;
        }
        Assert.assertTrue("a stream of format 8 was opened", refusal != null);
        Throwable c = refusal;
        while (!(c instanceof bergdb.storage.VersioningStreamException) && c.getCause() != null) {
            c = c.getCause();
        }
        Assert.assertTrue(String.valueOf(refusal), c instanceof bergdb.storage.VersioningStreamException
                && c.getMessage().contains("format version 8;")
                && c.getMessage().contains("release 2026.6"));
        Assert.assertEquals("nothing appended", bytes.length, old.getLength());
    }

    private static void checkCorruptReadSize(int reader) throws IOException {
        for (int size : new int[] {Integer.MAX_VALUE, 1 << 30, -1, 0, 6, 7}) {
            byte[] bytes = new byte[132];
            Bytes.intToBytesLE(size, bytes, 128);
            MemoryStream stream = new MemoryStream();
            stream.append(bytes, 0, bytes.length);
            NodeStream ns = new NodeStream(new RecoverableStream(stream, new MetaBlock()),
                    new Object());
            try {
                if (reader == 0) {
                    ns.readNode(128);
                } else if (reader == 1) {
                    ns.readTransBytes(128);
                } else {
                    ns.createTransIteratorFromExactStartupPos(128).next();
                }
                throw new AssertionError("bad size was accepted: " + size);
            } catch (StreamFormatException e) {
                Assert.assertTrue(e.getMessage(), e.getMessage().contains("size"));
            }
        }
    }

    /**
     * A node size of 8 to 11, below the node header's 12 bytes (bergdb 024-25), is refused
     * with a StreamFormatException, by readNode and by a record's parse, before the
     * checksum: NodeChecksum.sum throws an IllegalArgumentException for it, which would
     * escape the reads' failure handling (as 015-07's and 019-32's faults did).
     */
    @Nano
    private static void testNodeSizeBelowHeader() throws IOException {
        for (int size = 8; size < NodeChecksum.HEADER_SIZE; size++) {
            byte[] bytes = new byte[128 + 64];
            Bytes.intToBytesLE(size, bytes, 128);
            bytes[128 + 4] = Node.TYPE_DELETE;
            MemoryStream stream = new MemoryStream();
            stream.append(bytes, 0, bytes.length);
            NodeStream ns = new NodeStream(new RecoverableStream(stream, new MetaBlock()),
                    new Object());
            try {
                ns.readNode(128);
                throw new AssertionError("a node of " + size + " bytes was read");
            } catch (StreamFormatException e) {
                Assert.assertTrue(e.getMessage(), e.getMessage().contains("node size"));
            }
            try {
                NodeStream.bytesToNode(128, bytes, 128, size);
                throw new AssertionError("a node of " + size + " bytes was parsed");
            } catch (StreamFormatException e) {
                Assert.assertTrue(e.getMessage(), e.getMessage().contains("node size"));
            }
        }
    }

    /**
     * bergdb 021-14: a size at a position near Long.MAX_VALUE is refused; the check's
     * RecoverableStream.getSpos() overflowed, and it passed.
     */
    @Nano
    private static void testReadSizeNearMaxValue() {
        NodeStream.checkReadSize(200, 40, 1000);
        for (long pos : new long[] {961, 1000, 1001, Long.MAX_VALUE - 39, Long.MAX_VALUE - 7,
                Long.MAX_VALUE - 1}) {
            try {
                NodeStream.checkReadSize(pos, 40, 1000);
                throw new AssertionError("a size at " + pos + " was accepted");
            } catch (StreamFormatException e) {
                Assert.assertTrue(e.getMessage(), e.getMessage().contains("size"));
            }
        }
    }

    /** Meta blocks are not bytes available to a node or a record. */
    @Nano
    private static void testReadSizeExcludesMetaBlocks() throws IOException {
        byte[] bytes = new byte[RecoverableStream.META_BLOCK_DISTANCE + 144];
        int pos = RecoverableStream.META_BLOCK_DISTANCE - 8;
        Bytes.intToBytesLE(136, bytes, pos);  // Fits physically, but only 24 record bytes exist.
        MemoryStream stream = new MemoryStream();
        stream.append(bytes, 0, bytes.length);
        NodeStream ns = new NodeStream(new RecoverableStream(stream, new MetaBlock()),
                new Object());
        try {
            ns.readTransBytes(pos);
            throw new AssertionError("meta blocks counted as record bytes");
        } catch (StreamFormatException e) {
            Assert.assertTrue(e.getMessage(), e.getMessage().contains("size"));
        }
    }

    /** A last byte just before a meta block, and a read across one, are both valid. */
    @Nano
    private static void testReadSizeAtMetaBlock() throws IOException {
        int pos = RecoverableStream.META_BLOCK_DISTANCE - 32;
        for (int length : new int[] {200000, 200128, 200144}) {
            int size = length == 200144 ? 48 : 32;
            byte[] expected = new byte[size];
            Bytes.intToBytesLE(size, expected, 0);
            for (int i = 4; i < size; i++) {
                expected[i] = (byte) i;
            }
            byte[] bytes = new byte[length];
            for (int i = 0; i < size; i++) {
                bytes[(int) RecoverableStream.getSpos(pos, i)] = expected[i];
            }
            MemoryStream stream = new MemoryStream();
            stream.append(bytes, 0, bytes.length);
            NodeStream ns = new NodeStream(new RecoverableStream(stream, new MetaBlock()),
                    new Object());
            Assert.assertArrayEquals(expected, ns.readTransBytes(pos));
        }
    }

    /**
     * bergdb 028-56: recordHolding() while the stream is cut and reclaim's cut, 'cut', moves
     * on. The walk reads the cut, 0 here, then the meta block before 'tpos', which names the
     * record at 128; at that read the cut moves (CutAtReadStream), and the stream is cut to
     * the start of its 1 MB array, 1,000,000, which removes the named record, and the walk's
     * read there is below the first position. With the cut moved to a record at or before
     * 'tpos' (case 0), the walk starts again, from the new cut, and finds a record's start
     * at 'tpos'; before, the read was thrown, and Db.getTrans() expired a transaction that
     * is kept. With the cut moved past 'tpos' (case 1), or not moved (case 2), the read is
     * thrown as before, with ReadBelowFirstPosException as the cause: Db.getTrans() expires.
     */
    @Nano
    private static void testRecordHoldingCutDuringTheWalk() {
        for (int c = 0; c < 3; c++) {
            final CutAtReadStream stream = new CutAtReadStream();
            final RecoverableStream r = new RecoverableStream(stream, new MetaBlock());
            final NodeStream ns = new NodeStream(r, new Object());
            final long named = appendRecord(r, 1000);
            appendRecord(r, 1100 * 1000);       // over the array at 1,000,000
            final long newCut = appendRecord(r, 1000);
            final long tpos = appendRecord(r, 1000);
            final long pastTpos = appendRecord(r, 1000);
            final long array = 1000 * 1000;
            Assert.assertTrue("named " + named + ", the cut " + newCut + ", tpos " + tpos,
                    named < array && array < newCut && pastTpos < 2 * array);
            final long[] cut = {0};
            final long movedTo = c == 0 ? newCut : c == 1 ? pastTpos : 0;
            stream.blockPos = tpos / RecoverableStream.META_BLOCK_DISTANCE
                    * RecoverableStream.META_BLOCK_DISTANCE;
            stream.atRead = new Runnable() {
                public void run() {
                    cut[0] = movedTo;
                    stream.inner.pretruncate(newCut);
                }
            };
            try {
                Assert.assertEquals("case " + c, -1L, ns.recordHolding(tpos, () -> cut[0]));
                Assert.assertTrue("case " + c + ": walked", c == 0);
            } catch (StreamIoException e) {
                Assert.assertTrue("case " + c + ": " + e, c != 0
                        && e.getCause() instanceof ReadBelowFirstPosException);
            }
            Assert.assertEquals("case " + c + ": cut", array, stream.getFirstPos());
            Assert.assertTrue("case " + c + ": the meta block read", stream.atRead == null);
        }
    }

    /**
     * Appends a committed record of 'size' bytes, named by the meta blocks after it, as
     * NodeStream.appendNodes() does; returns its position.
     */
    private static long appendRecord(RecoverableStream r, int size) {
        final byte[] bytes = new byte[size];
        Bytes.intToBytesLE(size, bytes, 0);
        bytes[4] = StoredTrans.RECORD_FORMAT;
        bytes[size - 1] = RecoverableStream.LAST_BYTE;
        final long result = r.getNextSpos();
        r.append(bytes, 0, size, true, -1);
        r.getMetaBlock().setLastTransSpos(result);
        return result;
    }

    /**
     * A MemoryStream for testRecordHoldingCutDuringTheWalk (bergdb 028-56): 'atRead' runs
     * once, at the read of a meta block's first 8 bytes at 'blockPos', before the read.
     */
    private static final class CutAtReadStream implements AppendOnlyStream {
        final MemoryStream inner = new MemoryStream();
        long blockPos = -1;
        Runnable atRead;

        public long getLength() {
            return inner.getLength();
        }

        public long getFirstPos() {
            return inner.getFirstPos();
        }

        public void read(long position, byte[] dest, int destOffset, int length)
                throws IOException {
            final Runnable run = atRead;
            if (run != null && position == blockPos && length == 8) {
                atRead = null;
                run.run();
            }
            inner.read(position, dest, destOffset, length);
        }

        public void append(byte[] source, int sourceOffset, int length) throws IOException {
            inner.append(source, sourceOffset, length);
        }

        public void pretruncate(long position) {
            inner.pretruncate(position);
        }

        public void close() {
            inner.close();
        }
    }
    
    @Nano
    public static void testSimpleRestart() {
        MemoryStream mstream = new MemoryStream();
        CoreTestClock clock = new CoreTestClock();
        Db db = Db.builder().testSetup().mainStream(mstream).clock(clock).build();
        db.start();
        db.setStartupDistance(10000);
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
        ti.next();      // the creating start's startup distance (bergdb 028-15)
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
        Db db = Db.builder().testSetup(s).start();
        db.setStartupDistance(10);
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
     * cut. The creating start's record of the startup distance, after the primordial one
     * (bergdb 028-15), is cut off first.
     */
    @Nano
    public static void testCrashInPrimordialTrans() throws IOException, InterruptedException {
        MemoryStream s = new MemoryStream();
        Db.builder().testSetup(s).start().close();
        MemoryStream created = s.copy();    // close() closed s.
        created.truncate(Db.CREATION_LENGTH);
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
