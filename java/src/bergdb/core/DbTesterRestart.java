package bergdb.core;

import java.io.IOException;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashMap;
import java.util.IdentityHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Random;
import java.util.Set;
import java.util.TreeMap;

import bergdb.common.Bytes;
import bergdb.common.StringUtil;
import bergdb.dag.GetData;
import bergdb.dag.Keys;
import bergdb.dag.KeyNode;
import bergdb.dag.Klong;
import bergdb.dag.Node;
import bergdb.dag.NodeVisitor;
import bergdb.dag.TopNode;
import bergdb.dag.ValueNode;
import bergdb.nanotest.Assert;
import bergdb.nanotest.Nano;
import bergdb.pub.util.Clock;
import bergdb.pub.util.DbException;
import bergdb.pub.util.IllegalDbStateException;
import bergdb.pub.util.SyncLevel;
import bergdb.storage.RecoverableStream;
import bergdb.storage.StreamFormatException;
import bergdb.storage.VersioningStreamException;
import bergdb.stream.AppendOnlyStream;
import bergdb.stream.CutStream;
import bergdb.stream.MemoryStream;

/**
 * Class that tests restarting Db from an in-memory stream.
 * Typically a short startupDistance is used and eviction is often disabled.
 * 
 * @author Frans Lundberg
 */
public class DbTesterRestart {

    /** A corrupt record time must refuse startup before replay, with or without -ea. */
    @Nano
    public static void testCorruptRecordTimesRefused() throws IOException {
        MemoryStream stream = new MemoryStream();
        CoreTestClock clock = new CoreTestClock();
        long lastPos;
        try (Db db = Db.builder().testSetup(stream).clock(clock)
                .startupDistance(1000000).start()) {
            clock.setTime(10);
            db.execute(db.trans().put("/k1", "1"));
            clock.setTime(20);
            db.execute(db.trans().put("/k2", "2"));
            clock.setTime(30);
            Trans trans = db.trans().put("/k3", "3").build();
            db.execute(trans);
            lastPos = trans.tpos;
        }
        long[][] bad = {
            {lastPos, 20}, {lastPos, 10}, {lastPos, 0}, {lastPos, -1},
            {lastPos, Klong.MAX_TIME + 1}, {lastPos, Long.MAX_VALUE},
            {RecoverableStream.META_BLOCK_SIZE, -1},
            {RecoverableStream.META_BLOCK_SIZE, Klong.MAX_TIME + 1}
        };
        for (long[] b : bad) {
            MemoryStream corrupt = stream.copy();
            byte[] timeBytes = new byte[8];
            Bytes.longToBytesLE(b[1], timeBytes, 0);
            MemoryStream.TestAccess.write(corrupt, timeBytes, b[0] + 8);
            try (Db ignored = Db.builder().testSetup(corrupt).clock(clock)
                    .startupDistance(1000000).start()) {
                throw new AssertionError("started with corrupt record time " + b[1]);
            } catch (StreamFormatException expected) {
                String message = b[1] < 0 || b[1] > Klong.MAX_TIME
                        ? "Transaction time out of range" : "non-increasing tt";
                Assert.assertTrue(expected.getMessage(), expected.getMessage().contains(message));
            }
        }
    }

    /**
     * A record whose size field is larger than its content is refused (bergdb 015-72,
     * 016-06/R6, R6-F1): record A's size is set to A's and B's together, so that it ends on
     * B's last byte. Before the fix, the start succeeded and B's transaction, /b, was lost.
     */
    @Nano
    public static void testEnlargedRecordSizeRefused() throws IOException {
        MemoryStream stream = new MemoryStream();
        CoreTestClock clock = new CoreTestClock();
        long a, c;
        try (Db db = Db.builder().testSetup(stream).clock(clock)
                .startupDistance(1000000).start()) {
            clock.setTime(10);
            Trans t = db.trans().put("/a", "1").build();
            db.execute(t);
            a = t.tpos;
            clock.setTime(20);
            db.execute(db.trans().put("/b", "2"));
            clock.setTime(30);
            t = db.trans().put("/c", "3").build();
            db.execute(t);
            c = t.tpos;
        }
        MemoryStream corrupt = stream.copy();
        byte[] size = new byte[4];
        Bytes.intToBytesLE((int) (c - a), size, 0);     // A's size + B's: B's last byte
        MemoryStream.TestAccess.write(corrupt, size, a);
        try (Db db = Db.builder().testSetup(corrupt).clock(clock)
                .startupDistance(1000000).start()) {
            throw new AssertionError("started with A's size over B; /b = " 
                    + (DbUtil.get(db, Long.MAX_VALUE, "/b") == null ? "lost" : "found"));
        } catch (StreamFormatException expected) {
            Assert.assertTrue(expected.getMessage(), 
                    expected.getMessage().contains("its size says"));
        }
    }

    /**
     * A corrupt startupPos in the last record is refused with a StreamFormatException
     * (bergdb 015-75, 016-06/R6, R6-F4): negative, not a multiple of 8, in the first meta
     * block, or after the record's own position. Before the fix, -8 failed an assert, or
     * without -ea gave an IllegalArgumentException from the stream's read.
     */
    @Nano
    public static void testCorruptStartupPosRefused() throws IOException {
        MemoryStream stream = new MemoryStream();
        CoreTestClock clock = new CoreTestClock();
        long c;
        try (Db db = Db.builder().testSetup(stream).clock(clock)
                .startupDistance(1000000).start()) {
            clock.setTime(10);
            db.execute(db.trans().put("/a", "1"));
            clock.setTime(20);
            Trans t = db.trans().put("/b", "2").build();
            db.execute(t);
            c = t.tpos;
        }
        for (long sp : new long[] {-8, Long.MIN_VALUE, 4, 8, 120, c + 4, c + 8, c | (1L << 40)}) {
            MemoryStream corrupt = stream.copy();
            byte[] bytes = new byte[8];
            Bytes.longToBytesLE(sp, bytes, 0);
            MemoryStream.TestAccess.write(corrupt, bytes, c + 16);
            try (Db db = Db.builder().testSetup(corrupt).clock(clock)
                    .startupDistance(1000000).start()) {
                throw new AssertionError("started with startupPos " + sp);
            } catch (StreamFormatException expected) {
                Assert.assertTrue(expected.getMessage(), 
                        expected.getMessage().contains("startupPos " + sp));
            }
        }
    }

    /**
     * A got-dirty entry whose id is not the id of the node at its position is refused
     * with a StreamFormatException (bergdb 015-75, 016-06/R6, R6-F4). Before the fix, the
     * ids were compared by an assert only: without -ea the start succeeded, with -ea it
     * failed with an AssertionError.
     */
    @Nano
    public static void testCorruptGotDirtyIdRefused() throws IOException {
        MemoryStream stream = new MemoryStream();
        CoreTestClock clock = new CoreTestClock();
        long a;
        try (Db db = Db.builder().testSetup(stream).clock(clock)
                .startupDistance(1000000).start()) {
            clock.setTime(10);
            db.execute(db.trans().put("/a", "1").build());
            clock.setTime(20);
            db.execute(db.trans().put("/b", "2"));
            clock.setTime(30);
            db.execute(db.trans().put("/c", "3"));
        }
        
        // The first record after the primordial one, the creating start's of the startup
        // distance (bergdb 028-15; A's until then), holds the got-dirty entries; an entry
        // whose position is a node written before, at the creation.
        a = Db.CREATION_LENGTH;
        byte[] record = readRecord(stream, a);
        long[] dirty = StoredTrans.parse(a, record).gotDirtyIdsAndSpos;
        int entry = -1;
        for (int i = 0; i < dirty.length / 2 && entry < 0; i++) {
            if (bergdb.dag.Spos.isValid(dirty[2 * i + 1]) 
                    && !bergdb.dag.Spos.isVpos(dirty[2 * i + 1])) {
                entry = i;
            }
        }
        Assert.assertTrue("an entry with a stream position", entry >= 0);
        
        // The entry's 16 bytes, in the list before the last byte and the padding.
        int at = -1;
        for (int i = record.length - 16; i >= 0 && at < 0; i--) {
            if (Bytes.bytesToLongLE(record, i) == dirty[2 * entry] 
                    && Bytes.bytesToLongLE(record, i + 8) == dirty[2 * entry + 1]) {
                at = i;
            }
        }
        Assert.assertTrue("the entry's bytes", at > 0);
        
        MemoryStream corrupt = stream.copy();
        byte[] id = new byte[8];
        Bytes.longToBytesLE(123456789L, id, 0);
        MemoryStream.TestAccess.write(corrupt, id, a + at);
        try (Db db = Db.builder().testSetup(corrupt).clock(clock)
                .startupDistance(1000000).start()) {
            throw new AssertionError("started with got-dirty id 123456789");
        } catch (StreamFormatException expected) {
            Assert.assertTrue(expected.getMessage(), 
                    expected.getMessage().contains("123456789"));
        }
    }

    /**
     * A last record whose topPos names an older version of a top node than the newest
     * in the startup section is refused with a StreamFormatException (bergdb 015-75,
     * 016-06/R6, R6-F4). Before the fix, it was an assert only: without -ea the start took
     * the newer version, with -ea it failed with an AssertionError.
     */
    @Nano
    public static void testOlderTopPosRefused() throws IOException {
        MemoryStream stream = new MemoryStream();
        CoreTestClock clock = new CoreTestClock();
        ArrayList<Long> tposes = new ArrayList<Long>();
        try (Db db = Db.builder().testSetup(stream).clock(clock)
                .startupDistance(100).start()) {
            for (int i = 1; i <= 6; i++) {
                clock.setTime(10 * i);
                Trans t = db.trans().put("/k" + i, "" + i).build();
                db.execute(t);
                tposes.add(t.tpos);
            }
        }
        long last = tposes.get(tposes.size() - 1);
        StoredTrans lastTrans = StoredTrans.parse(last, readRecord(stream, last));
        long topPos = lastTrans.topPos;
        long id = -1;
        long older = -1;
        for (long tpos : tposes) {
            for (StoredNode n : StoredTrans.parse(tpos, readRecord(stream, tpos)).nodes) {
                Node node = n.getNode();
                if (node.getType() == Node.TYPE_TOP_NODE && node.getSpos() == topPos) {
                    id = node.getId();
                }
            }
        }
        for (long tpos : tposes) {
            for (StoredNode n : StoredTrans.parse(tpos, readRecord(stream, tpos)).nodes) {
                Node node = n.getNode();
                if (node.getType() == Node.TYPE_TOP_NODE && node.getId() == id 
                        && node.getSpos() < topPos) {
                    older = node.getSpos();
                }
            }
        }
        Assert.assertTrue("an older version of top node " + id + " at " + topPos, older > 0);
        
        MemoryStream corrupt = stream.copy();
        byte[] bytes = new byte[8];
        Bytes.longToBytesLE(older, bytes, 0);
        MemoryStream.TestAccess.write(corrupt, bytes, last + 24);
        try (Db db = Db.builder().testSetup(corrupt).clock(clock)
                .startupDistance(100).start()) {
            throw new AssertionError("started with topPos " + older + ", not " + topPos);
        } catch (StreamFormatException expected) {
            Assert.assertTrue(expected.getMessage(), 
                    expected.getMessage().contains("not the newest version"));
        }
    }

    /**
     * A meta block whose last transaction's position is past the stream's end is refused
     * with a StreamFormatException, and nothing is written (bergdb 019-34, found by harness
     * 6.1, bergdb 018-07: the first meta block's byte 23 flipped). Before the fix, recovery
     * threw an IllegalArgumentException ("spos >= streamSize").
     */
    @Nano
    public static void testMetaBlockLastTransPosRefused() throws IOException {
        MemoryStream stream = new MemoryStream();
        CoreTestClock clock = new CoreTestClock();
        try (Db db = Db.builder().testSetup(stream).clock(clock)
                .startupDistance(1000000).start()) {
            clock.setTime(10);
            db.execute(db.trans().put("/a", "1"));
            clock.setTime(20);
            db.execute(db.trans().put("/b", "2"));
        }
        for (int mask : new int[] {0x80, 0xff}) {
            MemoryStream corrupt = stream.copy();
            byte[] b = new byte[1];
            corrupt.read(23, b, 0, 1);
            b[0] ^= (byte) mask;
            MemoryStream.TestAccess.write(corrupt, b, 23);
            long length = corrupt.getLength();
            try (Db db = Db.builder().testSetup(corrupt).clock(clock)
                    .startupDistance(1000000).start()) {
                throw new AssertionError("started with byte 23 xor " + mask);
            } catch (StreamFormatException expected) {
                Assert.assertTrue(expected.getMessage(),
                        expected.getMessage().contains("names the last transaction at"));
            }
            Assert.assertEquals(length, corrupt.getLength());
        }
        // The second meta block, which a large value puts in the stream, naming a position
        // in the first meta block, or one after itself (bergdb 019-40): refused too.
        final MemoryStream large = stream.copy();     // A closed stream takes no append.
        try (Db db = Db.builder().testSetup(large).clock(clock)
                .startupDistance(1000000).start()) {
            clock.setTime(30);
            db.execute(db.trans().put("/c", new byte[RecoverableStream.META_BLOCK_DISTANCE]));
        }
        final long block = RecoverableStream.META_BLOCK_DISTANCE;
        for (long spos : new long[] {10, block + RecoverableStream.META_BLOCK_SIZE}) {
            MemoryStream corrupt = large.copy();
            byte[] b = new byte[8];
            Bytes.longToBytesLE(spos, b, 0);
            MemoryStream.TestAccess.write(corrupt, b, block + 16);
            try (Db db = Db.builder().testSetup(corrupt).clock(clock)
                    .startupDistance(1000000).start()) {
                throw new AssertionError("started with the last transaction at " + spos);
            } catch (StreamFormatException expected) {
                Assert.assertTrue(expected.getMessage(),
                        expected.getMessage().contains("names the last transaction at"));
            }
        }
    }

    /** The bytes of the record at 'tpos', which must not span a meta block. */
    /**
     * A crash inside the record that Db.setStartupDistance writes (bergdb 028-08; 028-15):
     * the setting is a KV of that record, so a crash anywhere before the record's end
     * starts with the old setting, the record aborted, and one at its end with the new; a
     * later start keeps what the first one read. Until bergdb 028-15 the setting was in the
     * meta block that the record held, with a dummy value of 200 kB, and a crash after that
     * block and before the record's end started with the new setting. The builder's setting
     * of the restarts, another, is not taken: the stream's is.
     */
    @Nano
    public static void testCrashInsideSetStartupDistance() throws IOException {
        MemoryStream stream = new MemoryStream();
        CoreTestClock clock = new CoreTestClock();
        long before, after;
        try (Db db = Db.builder().testSetup(stream).clock(clock)
                .startupDistance(1000000).start()) {
            clock.setTime(10);
            db.execute(db.trans().put("/a", "1"));
            before = db.getStreamLength();
            clock.setTime(20);
            db.setStartupDistance(2000000);
            after = db.getStreamLength();
            Assert.assertEquals(2000000, db.getStartupDistance());
        }
        Assert.assertTrue("a small record, " + (after - before), after - before < 1000);
        
        for (long cut = before; cut <= after; cut += cut + 8 < after ? 8 : 1) {
            MemoryStream m = stream.copy();
            m.truncate(cut);
            int expected = cut == after ? 2000000 : 1000000;
            for (int start = 0; start < 2; start++) {
                try (Db db = Db.builder().testSetup(m).clock(clock)
                        .startupDistance(3000000).start()) {
                    String at = "cut at " + cut + ", start " + start;
                    Assert.assertEquals(at, expected, db.getStartupDistance());
                    Assert.assertEquals(at, "1", DbUtil.getString(db, "/a"));
                    byte[] kv = db.getOne(Long.MAX_VALUE, DbConstants.SD_KEY, db.newGetData());
                    Assert.assertEquals(at, expected, Db.parseStartupDistance(kv));
                }
                m = m.copy();       // a closed MemoryStream refuses appends
            }
        }
    }

    /**
     * Bergdb 028-15: a crash inside the creating start's record of the startup distance, or
     * before it, after the primordial record: recovery cuts the record off, and the start,
     * which finds the primordial record alone and no KV, takes its builder's setting, which
     * it puts; a later start keeps that one. The whole record keeps the creation's setting,
     * whatever the builder of a later start says.
     */
    @Nano
    public static void testCrashInCreatingStartsKv() throws IOException {
        MemoryStream stream = new MemoryStream();
        CoreTestClock clock = new CoreTestClock();
        Db.builder().testSetup(stream).clock(clock).startupDistance(1000000).start().close();
        final long end = stream.getLength();
        Assert.assertTrue("a record after the creation", end > Db.CREATION_LENGTH);
        
        for (long cut = Db.CREATION_LENGTH; cut <= end; cut += cut + 8 < end ? 8 : 1) {
            MemoryStream m = stream.copy();
            m.truncate(cut);
            int expected = cut == end ? 1000000 : 2000000;
            for (int start = 0; start < 2; start++) {
                try (Db db = Db.builder().testSetup(m).clock(clock)
                        .startupDistance(start == 0 ? 2000000 : 3000000).start()) {
                    String at = "cut at " + cut + ", start " + start;
                    Assert.assertEquals(at, expected, db.getStartupDistance());
                    byte[] kv = db.getOne(Long.MAX_VALUE, DbConstants.SD_KEY, db.newGetData());
                    Assert.assertEquals(at, expected, Db.parseStartupDistance(kv));
                    Assert.assertEquals(at + ", the counters", 0, db.getTransactionCount());
                }
                m = m.copy();       // a closed MemoryStream refuses appends
            }
        }
    }
    
    /**
     * Bergdb 028-15 (option A; Frans, 2026-11-18, 10:50): a database of release 2026.5 or
     * earlier, its meta blocks of version 154, is refused at the start with a
     * VersioningStreamException whose message names release 2026.5 and says to make the
     * database again, and the start writes nothing.
     */
    @Nano
    public static void testVersion154Refused() throws IOException {
        MemoryStream s = new MemoryStream();
        CoreTestClock clock = new CoreTestClock();
        try (Db db = Db.builder().testSetup(s).clock(clock).start()) {
            clock.setTime(10);
            db.execute(db.trans().put("/k", new byte[300 * 1000]).build());     // two blocks
        }
        MemoryStream m = s.copy();
        for (long pos = 0; pos + 128 <= m.getLength();
                pos += RecoverableStream.META_BLOCK_DISTANCE) {
            MemoryStream.TestAccess.write(m, new byte[] {(byte) 154, 0, 0, 0}, pos + 4);
        }
        byte[] before = bytesOf(m);
        try (Db db = Db.builder().testSetup(m).clock(clock).start()) {
            throw new AssertionError("started a database of version 154");
        } catch (VersioningStreamException e) {
            Assert.assertTrue(e.getMessage(), e.getMessage().contains("release 2026.5")
                    && e.getMessage().contains("make the database again"));
        }
        Assert.assertArrayEquals("the stream as it was", before, bytesOf(m));
    }
    
    /**
     * Bergdb 028-15: the startup distance is a KV, read at the end of a start. A change by
     * setStartupDistance() is kept over restarts, whatever the builder of a restart says, and
     * the meta blocks' bytes 40 to 43, where it was until the meta block's version 155, are
     * zero in every block. A KV of other bytes is refused at the start with an
     * InternalDataException; a stream with records after the primordial one and no KV with a
     * StreamFormatException, as damaged.
     */
    @Nano
    public static void testStartupDistanceKvKept() throws IOException {
        MemoryStream stream = new MemoryStream();
        CoreTestClock clock = new CoreTestClock();
        try (Db db = Db.builder().testSetup(stream).clock(clock).start()) {
            Assert.assertEquals(50 * 1000000, db.getStartupDistance());     // the default
            clock.setTime(10);
            db.execute(db.trans().put("/a", new byte[300 * 1000]).build());  // meta blocks
            db.setStartupDistance(700 * 1000);
            Assert.assertEquals(700 * 1000, db.getStartupDistance());
        }
        for (int start = 0; start < 2; start++) {
            stream = stream.copy();
            try (Db db = Db.builder().testSetup(stream).clock(clock)
                    .startupDistance(1234567).start()) {
                Assert.assertEquals("start " + start, 700 * 1000, db.getStartupDistance());
                if (start == 1) {
                    db.setStartupDistance(800 * 1000);
                }
            }
        }
        stream = stream.copy();
        try (Db db = Db.builder().testSetup(stream).clock(clock).start()) {
            Assert.assertEquals("after the second change", 800 * 1000, db.getStartupDistance());
        }
        final int md = RecoverableStream.META_BLOCK_DISTANCE;
        Assert.assertTrue("two meta blocks", stream.getLength() > md + 128);
        for (long pos = 0; pos + 128 <= stream.getLength(); pos += md) {
            byte[] block = new byte[128];
            stream.read(pos, block, 0, block.length);
            for (int i = 40; i < 44; i++) {
                Assert.assertEquals("block at " + pos + ", byte " + i, 0, block[i]);
            }
        }
        
        byte[][] bad = {{1, 2, 3}, {9, 0, 0, 0}, {1, (byte) 0xca, (byte) 0x9a, 0x3b},
                {0, 0, 0, (byte) 0x80}, {0x20, (byte) 0xa1, 0x07, 0, 0}};
        for (byte[] value : bad) {
            MemoryStream m = stream.copy();
            try (Db db = Db.builder().testSetup(m).clock(clock).start()) {
                db.execute(db.trans().putCore(DbConstants.SD_KEY, value).build());
            }
            try (Db db = Db.builder().testSetup(m.copy()).clock(clock).start()) {
                throw new AssertionError("started with " + Arrays.toString(value));
            } catch (InternalDataException e) {
                Assert.assertTrue(e.getMessage(), e.getMessage().contains(
                        "Bad value of /#i/-sd"));
            }
        }
        
        MemoryStream m = stream.copy();
        try (Db db = Db.builder().testSetup(m).clock(clock).start()) {
            db.execute(db.trans().deleteCore(DbConstants.SD_KEY).build());
        }
        try (Db db = Db.builder().testSetup(m.copy()).clock(clock).start()) {
            throw new AssertionError("started without the KV");
        } catch (StreamFormatException e) {
            Assert.assertTrue(e.getMessage(), e.getMessage().contains("has no startup distance"));
        }
    }
    
    /**
     * Bergdb 028-15: reclaim's cuts leave the startup distance's KV live. The creation's
     * setting, 1000 bytes, and a later one, both cut away with their records, are kept: the
     * KV is copied forward as any live KV, and a start after the cuts reads the last
     * setting.
     */
    @Nano
    public static void testStartupDistanceKvAfterReclaimCut() throws IOException {
        MemoryStream stream = new MemoryStream();
        CoreTestClock clock = new CoreTestClock();
        long setterEnd = 0;
        Db db = Db.builder().testSetup(stream).clock(clock).startupDistance(1000)
                .maxNodeSize8().start();
        try {
            Random rnd = new Random(1);
            for (int i = 1; i <= 3000; i++) {
                clock.setTime(i * Clock.UNITS_PER_SEC / 10);
                byte[] value = new byte[1 + rnd.nextInt(200)];
                rnd.nextBytes(value);
                db.execute(db.trans().put("/k/" + rnd.nextInt(500), value));
                if (i == 100) {
                    db.setRetainDuration(1 * Clock.UNITS_PER_SEC);
                }
                if (i == 1500) {
                    db.setStartupDistance(400 * 1000);      // the least that the call sets
                    setterEnd = db.getStreamLength();
                }
            }
            for (int i = 3001; i <= 9000 && db.getFirstAvailablePos() <= setterEnd; i++) {
                clock.setTime(i * Clock.UNITS_PER_SEC / 10);
                byte[] value = new byte[1 + rnd.nextInt(200)];
                rnd.nextBytes(value);
                db.execute(db.trans().put("/k/" + rnd.nextInt(500), value));
            }
            db.sync(SyncLevel.ORDINARY);
            Assert.assertTrue("cut past the setter's record, " + db.getFirstAvailablePos()
                    + " <= " + setterEnd, db.getFirstAvailablePos() > setterEnd);
            GetData gd = db.newGetData();
            Assert.assertTrue("the KV", db.getOne(Long.MAX_VALUE, DbConstants.SD_KEY, gd) != null);
            Assert.assertTrue("the KV's record after the cut",
                    gd.tpos >= db.getFirstAvailablePos());
        } finally {
            db.close();
        }
        try (Db again = Db.builder().testSetup(stream.copy()).clock(clock).maxNodeSize8()
                .start()) {
            Assert.assertEquals(400 * 1000, again.getStartupDistance());
        }
    }
    
    /**
     * A last record whose startupPos is its own position is refused with a
     * StreamFormatException (bergdb 028-09): the take never writes it, as a record's take
     * takes the transactions before it only (TransSeq.take, s(i) < i). Before the fix, the
     * start took a section of that record alone, whose transaction a start does not rerun:
     * with no index node in the record, every key was gone, and the next commit wrote the
     * same startupPos, so a later start lost them too.
     */
    @Nano
    public static void testOwnPositionStartupPosRefused() throws IOException {
        MemoryStream stream = new MemoryStream();
        CoreTestClock clock = new CoreTestClock();
        long c = 0;
        try (Db db = Db.builder().testSetup(stream).clock(clock)
                .startupDistance(1000000).start()) {
            for (int i = 1; i <= 4; i++) {
                clock.setTime(10 * i);
                Trans t = db.trans().put("/k" + i, "" + i).build();
                db.execute(t);
                c = t.tpos;
                Assert.assertTrue("s(i) < i", t.startupPos < t.tpos);
            }
        }
        MemoryStream corrupt = stream.copy();
        byte[] bytes = new byte[8];
        Bytes.longToBytesLE(c, bytes, 0);
        MemoryStream.TestAccess.write(corrupt, bytes, c + 16);
        try (Db db = Db.builder().testSetup(corrupt).clock(clock)
                .startupDistance(1000000).start()) {
            throw new AssertionError("started with startupPos " + c + ", its own; /k1 = " 
                    + DbUtil.getString(db, "/k1"));
        } catch (StreamFormatException expected) {
            Assert.assertTrue(expected.getMessage(), 
                    expected.getMessage().contains("startupPos " + c));
        }
    }

    private static byte[] readRecord(MemoryStream stream, long tpos) throws IOException {
        byte[] size = new byte[4];
        stream.read(tpos, size, 0, 4);
        byte[] record = new byte[Bytes.bytesToIntLE(size, 0)];
        stream.read(tpos, record, 0, record.length);
        return record;
    }

    /** Real read results carried to a new Db: bergdb 005-70, option A. */
    @Nano
    public static void testStmAfterRestart() {
        for (int startupDistance : new int[] {100, 1000000}) {
            MemoryStream stream = new MemoryStream();
            CoreTestClock clock = new CoreTestClock();
            long oldReadTime;
            long boundary;
            try (Db db = Db.builder().testSetup(stream).clock(clock)
                    .startupDistance(startupDistance).start()) {
                clock.setTime(10);
                db.execute(db.trans().put("/k", "1"));
                GetData read = db.newGetData();
                Assert.assertArrayEquals(StringUtil.toBytes("1"),
                        db.getOne(Long.MAX_VALUE, Keys.toSegments("/k"), read));
                oldReadTime = read.actualLookupTime;
                clock.setTime(20);
                db.execute(db.trans().put("/k", "2"));
                // The boundary is the last commit, including one without writes.
                clock.setTime(30);
                db.execute(db.trans().build());
                db.getOne(Long.MAX_VALUE, Keys.toSegments("/k"), read);
                boundary = read.actualLookupTime;
                assertStmRefused(db, oldReadTime);
            }
            try (Db db = Db.builder().testSetup(stream.copy()).clock(clock)
                    .startupDistance(startupDistance).start()) {
                assertStmRefused(db, oldReadTime);
                // An empty commit must not erase the boundary either.
                db.execute(db.trans().build());
                assertStmRefused(db, oldReadTime);
                // Equality is safe. The first unrelated write must preserve coverage.
                db.execute(db.trans().lookupTime(boundary).keyRead("/k").put("/j", "1"));
                db.execute(db.trans().lookupTime(boundary).keyRead("/k").put("/j", "2"));
                Assert.assertArrayEquals(StringUtil.toBytes("2"), DbUtil.get(db, Long.MAX_VALUE, "/j"));
                // New writes still conflict normally; reads after them can commit.
                db.execute(db.trans().put("/k", "3"));
                assertStmRefused(db, boundary);
                GetData read = db.newGetData();
                db.getOne(Long.MAX_VALUE, Keys.toSegments("/k"), read);
                db.execute(db.trans().lookupTime(read.actualLookupTime)
                        .keyRead("/k").put("/j", "3"));
                // Without read dependencies there is nothing for the STM to validate.
                db.execute(db.trans().lookupTime(oldReadTime).put("/j", "4"));
            }
        }
    }

    private static void assertStmRefused(Db db, long readTime) {
        long length = db.getStreamLength();
        byte[] before = DbUtil.get(db, Long.MAX_VALUE, "/j");
        try {
            db.execute(db.trans().lookupTime(readTime).keyRead("/k").put("/j", "stale"));
            throw new AssertionError("committed a stale read set at " + readTime);
        } catch (RerunException expected) {
            Assert.assertEquals(length, db.getStreamLength());
            Assert.assertArrayEquals(before, DbUtil.get(db, Long.MAX_VALUE, "/j"));
        }
    }

    @Nano
    public static void test0() {
        // Simple restart, Db with one single value.
        
        byte[] value;
        MemoryStream stream = new MemoryStream();
        CoreTestClock clock = new CoreTestClock();
        Db db = Db.builder().testSetup(stream).clock(clock).testId().start();
        clock.setTime(10);
        Trans trans = db.trans().put("admin1", "Sanna").build();
        db.execute(trans);
        db.sync(SyncLevel.ORDINARY);
        long tt = trans.tt;
        stream = stream.copy();
        
        db.close();
        Db db2 = Db.builder().testSetup().mainStream(stream).start();
        
        value = DbUtil.get(db2, Long.MAX_VALUE, "admin1");
        Assert.assertArrayEquals(StringUtil.toBytes("Sanna"), value);
        
        value = DbUtil.get(db2, tt-1, StringUtil.toBytes("admin1"));
        Assert.assertNull(value);
        
        value = DbUtil.get(db2, tt, "admin1");
        Assert.assertArrayEquals(StringUtil.toBytes("Sanna"), value);
        db2.close();
    }
    

    @Nano
    public static void testRestartOfEmptyDatabase() {
        MemoryStream stream = new MemoryStream();
        CoreTestClock clock = new CoreTestClock();
        Db db = Db.builder().testSetup(stream).clock(clock).testId().start();
        clock.setTime(10);
        db.sync(SyncLevel.ORDINARY);
        
        long c1 = DbUtil.checksum(db);
        
        stream = stream.copy();
        
        db.close();
        Db db2 = Db.builder().testSetup().mainStream(stream).start();
        
        long c2 = DbUtil.checksum(db2);
        
        Assert.assertEquals(c1, c2);
        db2.close();
    }
    
    @Nano
    public static void longerThanStartup() {
        // Stream is longer than startupDistance, single key, value updated many times.
        
        MemoryStream stream = new MemoryStream();
        CoreTestClock clock = new CoreTestClock();
        clock.setTime(2);
        Db db = Db.builder().testSetup(stream)
                .clock(clock).startupDistance(10*1000).start();
        byte[] bytes = new byte[1000];
        
        for (int i = 0; i < 20; i++) {
            clock.setTime(100 + i*10);
            bytes[0] = (byte) i;
            Trans trans = db.trans().put("k", bytes).build();
            db.execute(trans);
        }
        long sum1 = DbUtil.checksum(db);
        db.sync(SyncLevel.ORDINARY);
        db.stop();
        db = null;
        
        Db db2 = Db.builder().testSetup().mainStream(stream).start();
        Assert.assertNull(DbUtil.get(db2, 5, "k"));
        
        for (int i = 0; i < 20; i++) {
            long lookupTime = 100 + i*10 + 5;
            byte[] v = DbUtil.get(db2, lookupTime, "k");
            Assert.assertTrue(v != null);
            Assert.assertEquals(i, v[0]);
        }
        
        long sum2 = DbUtil.checksum(db2);
        Assert.assertEquals("checksum", sum1, sum2);
        
        db2.stop();
    }
    
    /**
     * Db should remember startupDistance after restart of initial state database.
     */
    @Nano
    private static void dbShouldRememberStartupDistance1() throws InterruptedException {
        final int startupDistance = 400 * 1000;
        MemoryStream stream = new MemoryStream();
        CoreTestClock clock = new CoreTestClock();
        
        Db db = Db.builder().testSetup(stream).clock(clock).startupDistance(startupDistance).start();
        Assert.assertEquals("before restart", startupDistance, db.getStartupDistance());
        db.sync(SyncLevel.ORDINARY);
        
        // Restart
        
        long streamLength = stream.getLength();
        Assert.assertTrue("" + streamLength, streamLength > RecoverableStream.META_BLOCK_SIZE);
        
        stream = stream.copy();
        Assert.assertTrue(stream.getLength() > RecoverableStream.META_BLOCK_SIZE);
        
        db.close();
        db = Db.builder().mainStream(stream).start();
        
        Assert.assertEquals("after restart", startupDistance, db.getStartupDistance());
        db.close();
    }
    
    /**
     * Db should remember startupDistance after one user transaction.
     */
    @Nano
    private static void dbShouldRememberStartupDistance2() throws InterruptedException {
        int startupDistance = 400 * 1000;
        MemoryStream stream = new MemoryStream();
        CoreTestClock clock = new CoreTestClock();
        
        Db db = Db.builder().testSetup(stream).clock(clock).startupDistance(startupDistance).start();
        db.execute(db.trans().put("key", "value"));
        Assert.assertEquals("before restart", startupDistance, db.getStartupDistance());
        db.sync(SyncLevel.ORDINARY);
        
        // Restart
        
        stream = stream.copy();
        db.close();
        db = Db.builder()
                .mainStream(stream)
                .clock(clock)
                .start();
        
        Assert.assertEquals("after restart", startupDistance, db.getStartupDistance());
        db.close();
    }
    
    // ======== Reclaim's settings kept in the stream, bergdb 015-87 ========
    
    /**
     * Bergdb 015-87, the restart test: the retain duration and the internal fraction, set
     * once after commit 100 and never again, are kept over restarts, right after the call
     * and after every 50 commits, so the stream from the decided cut is the one of the run
     * without restarts (010-P2). Before 015-87 a start took the builder's retain duration,
     * forever, and the default fraction: after the first restart no iteration started and
     * no cut was made, and the streams parted at commit 101.
     */
    @Nano("f")
    private static void testReclaimSettingsKeptOverRestarts() throws IOException {
        Object[] plain = settingsRun(false);
        Object[] restarts = settingsRun(true);
        Assert.assertEquals("the decided cut", plain[0], restarts[0]);
        Assert.assertEquals("the stream's length", plain[1], restarts[1]);
        Assert.assertArrayEquals("the stream from the decided cut", (byte[]) plain[2],
                (byte[]) restarts[2]);
    }
    
    /**
     * The workload of testReclaimSettingsKeptOverRestarts: 2000 commits, one every 0.1 s,
     * retain duration 1 s and internal fraction 0.1 set once, after commit 100. Returns the
     * decided cut, the length and the bytes from the cut; checks that reclaim cut.
     */
    private static Object[] settingsRun(boolean restarts) throws IOException {
        MemoryStream stream = new MemoryStream();
        CoreTestClock clock = new CoreTestClock();
        Db db = Db.builder().testSetup(stream).clock(clock).startupDistance(1000)
                .maxNodeSize8().start();
        try {
            Random rnd = new Random(1);
            for (int i = 1; i <= 2000; i++) {
                clock.setTime(i * Clock.UNITS_PER_SEC / 10);
                byte[] value = new byte[1 + rnd.nextInt(40)];
                rnd.nextBytes(value);
                db.execute(db.trans().put("/k/" + rnd.nextInt(500), value));
                if (i == 100) {
                    db.setRetainDuration(1 * Clock.UNITS_PER_SEC);
                    db.setReclaimInternalFraction(0.1);
                }
                if (restarts && i >= 100 && i % 50 == 0 && i < 2000) {
                    db.sync(SyncLevel.ORDINARY);
                    db.stop();
                    stream = stream.copy();
                    db = Db.builder().testSetup(stream).clock(clock).startupDistance(1000)
                            .maxNodeSize8().start();    // The settings not set again.
                    Assert.assertEquals("retain after a restart", 1 * Clock.UNITS_PER_SEC,
                            db.getRetainDuration());
                    Assert.assertTrue("fraction after a restart",
                            db.getInternalFraction() == 6554 / 65536.0);
                }
            }
            db.sync(SyncLevel.ORDINARY);
            long cut = Math.max(stream.getFirstPos(), db.getFirstAvailablePos());
            Assert.assertTrue("reclaim cut, restarts=" + restarts, db.getFirstAvailablePos() > 0);
            byte[] bytes = new byte[(int) (stream.getLength() - cut)];
            stream.read(cut, bytes, 0, bytes.length);
            return new Object[] {cut, stream.getLength(), bytes};
        } finally {
            db.stop();
        }
    }
    
    /**
     * Bergdb 015-87, F6: a call of setRetainDuration or setReclaimInternalFraction that is
     * refused changes nothing: on a stopped database (IllegalDbStateException) nothing is
     * written, and the values in force, also after a restart, are the old ones; an argument
     * out of range (IllegalArgumentException) changes nothing either.
     */
    @Nano
    private static void testRefusedReclaimSettingChangesNothing() {
        MemoryStream stream = new MemoryStream();
        CoreTestClock clock = new CoreTestClock();
        Db db = Db.builder().testSetup(stream).clock(clock).start();
        clock.setTime(10);
        db.execute(db.trans().put("/k", "1"));
        db.setRetainDuration(5 * Clock.UNITS_PER_SEC);
        db.setReclaimInternalFraction(0.5);
        final long length = db.getStreamLength();
        
        for (int i = 0; i < 4; i++) {
            boolean refused = false;
            try {
                if (i == 0) db.setRetainDuration(Clock.UNITS_PER_SEC - 1);
                if (i == 1) db.setRetainDuration(-1);
                if (i == 2) db.setReclaimInternalFraction(0.95);
                if (i == 3) db.setReclaimInternalFraction(Double.NaN);
            } catch (IllegalArgumentException expected) {
                refused = true;
            }
            Assert.assertTrue("refused " + i, refused);
        }
        Assert.assertEquals("nothing written", length, db.getStreamLength());
        db.sync(SyncLevel.ORDINARY);
        db.stop();
        
        for (int i = 0; i < 2; i++) {
            boolean refused = false;
            try {
                if (i == 0) db.setRetainDuration(7 * Clock.UNITS_PER_SEC);
                if (i == 1) db.setReclaimInternalFraction(0.3);
            } catch (IllegalDbStateException expected) {
                refused = true;
            }
            Assert.assertTrue("refused on a stopped database " + i, refused);
        }
        Assert.assertEquals("retain unchanged", 5 * Clock.UNITS_PER_SEC, db.getRetainDuration());
        Assert.assertTrue("fraction unchanged", db.getInternalFraction() == 0.5);
        Assert.assertEquals("nothing written on a stopped database", length, stream.getLength());
        
        db = Db.builder().testSetup(stream.copy()).clock(clock).start();
        Assert.assertEquals("retain after the restart", 5 * Clock.UNITS_PER_SEC,
                db.getRetainDuration());
        Assert.assertTrue("fraction after the restart", db.getInternalFraction() == 0.5);
        db.stop();
    }
    
    /**
     * Bergdb 015-87, F6: a call with the value in force writes nothing; a call with another
     * value writes one record, and the value is in force when it returns.
     */
    @Nano
    private static void testReclaimSettingInForceWritesNothing() {
        MemoryStream stream = new MemoryStream();
        CoreTestClock clock = new CoreTestClock();
        Db db = Db.builder().testSetup(stream).clock(clock).start();
        clock.setTime(10);
        db.execute(db.trans().put("/k", "1"));
        Assert.assertEquals("a new database: forever", Long.MAX_VALUE, db.getRetainDuration());
        Assert.assertTrue("a new database: 0.25", db.getInternalFraction() == 0.25);
        
        long length = db.getStreamLength();
        db.setRetainDuration(Long.MAX_VALUE);
        db.setReclaimInternalFraction(0.25);
        Assert.assertEquals("the defaults in force", length, db.getStreamLength());
        
        db.setRetainDuration(3 * Clock.UNITS_PER_SEC);
        Assert.assertTrue("a new value written", db.getStreamLength() > length);
        Assert.assertEquals("in force", 3 * Clock.UNITS_PER_SEC, db.getRetainDuration());
        length = db.getStreamLength();
        db.setRetainDuration(3 * Clock.UNITS_PER_SEC);
        Assert.assertEquals("the same value", length, db.getStreamLength());
        
        db.setReclaimInternalFraction(0.1);
        Assert.assertTrue("a new fraction written", db.getStreamLength() > length);
        length = db.getStreamLength();
        db.setReclaimInternalFraction(0.1);
        Assert.assertEquals("the same fraction", length, db.getStreamLength());
        
        Assert.assertEquals("the KV", "retain=" + 3 * Clock.UNITS_PER_SEC + "\nfraction=6554\n",
                StringUtil.toString(DbUtil.get(db, Long.MAX_VALUE, Reclaim.SETTINGS_KEY_NAME)));
        db.stop();
    }
    
    /**
     * Bergdb 015-87: the internal fraction is kept across a restart, and so is the retain
     * duration forever after a finite one (the KV holds both, whatever was set last).
     */
    @Nano
    private static void testReclaimSettingsKeptAcrossRestart() {
        MemoryStream stream = new MemoryStream();
        CoreTestClock clock = new CoreTestClock();
        Db db = Db.builder().testSetup(stream).clock(clock).start();
        clock.setTime(10);
        db.setReclaimInternalFraction(0.001);
        db.sync(SyncLevel.ORDINARY);
        db.stop();
        
        stream = stream.copy();
        db = Db.builder().testSetup(stream).clock(clock).start();
        Assert.assertTrue("fraction", db.getInternalFraction() == 66 / 65536.0);
        Assert.assertEquals("retain", Long.MAX_VALUE, db.getRetainDuration());
        db.setRetainDuration(2 * Clock.UNITS_PER_SEC);
        db.setRetainDuration(Long.MAX_VALUE);
        db.sync(SyncLevel.ORDINARY);
        db.stop();
        
        db = Db.builder().testSetup(stream.copy()).clock(clock).start();
        Assert.assertTrue("fraction, second restart", db.getInternalFraction() == 66 / 65536.0);
        Assert.assertEquals("retain, second restart", Long.MAX_VALUE, db.getRetainDuration());
        db.stop();
    }
    
    /**
     * Bergdb 015-87, design 005-78 Q6: the settings KV, written once at the start of the
     * stream, survives reclaim's cuts (reclaim's steps rewrite it as any live value): it is
     * found after three cuts or more, past its record, and a restart on the cut stream
     * finds it and goes on cutting.
     */
    @Nano("f")
    private static void testReclaimSettingsSurviveCuts() {
        CutStream stream = new CutStream();
        CoreTestClock clock = new CoreTestClock();
        clock.setTime(Clock.UNITS_PER_SEC);
        Db db = Db.builder().testSetup(stream).clock(clock).startupDistance(1000)
                .maxNodeSize8().start();
        db.setRetainDuration(1 * Clock.UNITS_PER_SEC);
        final long settingsEnd = db.getStreamLength();
        final String kv = "retain=" + Clock.UNITS_PER_SEC + "\nfraction=16384\n";
        Random rnd = new Random(2);
        int i = 0;
        int cuts = 0;
        long firstPos = stream.getFirstPos();
        while (cuts < 3 || firstPos <= settingsEnd || i < 1000) {
            Assert.assertTrue("cuts within 20,000 commits", i < 20000);
            i++;
            clock.setTime(Clock.UNITS_PER_SEC + i * Clock.UNITS_PER_SEC / 10);
            db.execute(db.trans().put("/k/" + rnd.nextInt(100), "v" + i));
            if (stream.getFirstPos() != firstPos) {
                cuts++;
                firstPos = stream.getFirstPos();
            }
        }
        Assert.assertTrue("the front is cut past the settings record",
                stream.getFirstPos() > settingsEnd);
        Assert.assertEquals("the KV after " + cuts + " cuts", kv,
                StringUtil.toString(DbUtil.get(db, Long.MAX_VALUE, Reclaim.SETTINGS_KEY_NAME)));
        db.sync(SyncLevel.ORDINARY);
        db.stop();
        
        stream = stream.copy();
        db = Db.builder().testSetup(stream).clock(clock).startupDistance(1000)
                .maxNodeSize8().start();
        Assert.assertEquals("after a restart on the cut stream", 1 * Clock.UNITS_PER_SEC,
                db.getRetainDuration());
        final long firstPosAtRestart = stream.getFirstPos();
        for (int k = 0; k < 1000; k++) {
            i++;
            clock.setTime(Clock.UNITS_PER_SEC + i * Clock.UNITS_PER_SEC / 10);
            db.execute(db.trans().put("/k/" + rnd.nextInt(100), "v" + i));
        }
        Assert.assertTrue("cuts after the restart", stream.getFirstPos() > firstPosAtRestart);
        Assert.assertEquals("the KV after the restart's cuts", kv,
                StringUtil.toString(DbUtil.get(db, Long.MAX_VALUE, Reclaim.SETTINGS_KEY_NAME)));
        db.stop();
    }
    
    /**
     * Bergdb 015-87, F5's option 1: a database whose settings were never set has no settings
     * KV, as its creation and its transactions write none, and a start on its stream runs
     * with the defaults, forever and 16,384 units (0.25); so does a stream written before
     * 015-87.
     */
    @Nano
    private static void testStreamWithoutSettingsHasDefaults() {
        MemoryStream stream = new MemoryStream();
        CoreTestClock clock = new CoreTestClock();
        Db db = Db.builder().testSetup(stream).clock(clock).start();
        for (int i = 1; i <= 20; i++) {
            clock.setTime(10 * i);
            db.execute(db.trans().put("/k/" + i, "v" + i));
        }
        Assert.assertTrue("no settings KV",
                DbUtil.get(db, Long.MAX_VALUE, Reclaim.SETTINGS_KEY_NAME) == null);
        db.sync(SyncLevel.ORDINARY);
        db.stop();
        
        db = Db.builder().testSetup(stream.copy()).clock(clock).start();
        Assert.assertTrue("no settings KV after the restart",
                DbUtil.get(db, Long.MAX_VALUE, Reclaim.SETTINGS_KEY_NAME) == null);
        Assert.assertEquals("forever", Long.MAX_VALUE, db.getRetainDuration());
        Assert.assertTrue("0.25", db.getInternalFraction() == 0.25);
        db.stop();
    }
    
    /**
     * Bergdb 015-87: a start refuses a settings KV in another form than the one that
     * Reclaim.setSettings writes, with an InternalDataException, as it refuses a bad table:
     * a number that is not one, or out of range; a line missing, of its own, or out of
     * order; a sign, a leading zero, or no newline at the end. The KV is put here by an
     * internal transaction, as only the database writes it; the well-formed value starts.
     */
    @Nano
    private static void testMalformedSettingsRefusedAtStart() {
        final long sec = Clock.UNITS_PER_SEC;
        final String good = "retain=" + sec + "\nfraction=16384\n";
        final String[] bad = {
            "retain=x\nfraction=16384\n",
            "retain=" + (sec - 1) + "\nfraction=16384\n",
            "retain=" + sec + "\nfraction=65\n",
            "retain=" + sec + "\nfraction=58983\n",
            "retain=" + sec + "\n",
            "fraction=16384\n",
            "",
            good + "other=1\n",
            "fraction=16384\nretain=" + sec + "\n",
            "retain=+" + sec + "\nfraction=16384\n",
            "retain=0" + sec + "\nfraction=16384\n",
            "retain=" + sec + "\nfraction=16384",
            "retain=" + sec + "\r\nfraction=16384\r\n",
        };
        for (int i = -1; i < bad.length; i++) {
            MemoryStream stream = new MemoryStream();
            CoreTestClock clock = new CoreTestClock();
            Db db = Db.builder().testSetup(stream).clock(clock).start();
            clock.setTime(10);
            // The Core's own put: a caller's is refused since bergdb 024-37.
            Trans t = db.trans().putCore(Keys.toSegments(Reclaim.SETTINGS_KEY_NAME),
                    StringUtil.toBytes(i < 0 ? good : bad[i])).build();
            t.isInternal = true;
            db.execute(t);
            db.sync(SyncLevel.ORDINARY);
            db.stop();
            
            String message = null;
            try {
                Db db2 = Db.builder().testSetup(stream.copy()).clock(clock).start();
                long retain = db2.getRetainDuration();
                db2.stop();
                Assert.assertEquals("the well-formed value", sec, retain);
            } catch (InternalDataException e) {
                message = e.getMessage();
            }
            Assert.assertTrue("value " + i + ", refused: " + message,
                    (i >= 0) == (message != null && message.contains(Reclaim.SETTINGS_KEY_NAME)));
        }
    }
    
    /**
     * Bergdb 015-87, F6: a setter call whose commit is refused before its go point (a clock
     * out of range, bergdb 005-18) leaves the settings in force as they were and writes
     * nothing, and the database goes on: the next call, with the clock back in range,
     * writes and is in force.
     */
    @Nano
    private static void testReclaimSettingRefusedAtGoPoint() {
        final long[] now = {1000};
        Clock clock = new Clock() {
            public long getTime() {
                return now[0];
            }
        };
        Db db = Db.builder().testSetup(new MemoryStream()).clock(clock).start();
        db.execute(db.trans().put("/k", "1"));
        final long length = db.getStreamLength();
        
        now[0] = Klong.MAX_TIME + 1;
        for (int i = 0; i < 2; i++) {
            String message = null;
            try {
                if (i == 0) db.setRetainDuration(5 * Clock.UNITS_PER_SEC);
                if (i == 1) db.setReclaimInternalFraction(0.5);
            } catch (DbException e) {
                message = e.getMessage();
            }
            Assert.assertTrue("refused " + i + ": " + message,
                    message != null && message.contains("outside the range"));
        }
        Assert.assertEquals("retain unchanged", Long.MAX_VALUE, db.getRetainDuration());
        Assert.assertTrue("fraction unchanged", db.getInternalFraction() == 0.25);
        Assert.assertEquals("nothing written", length, db.getStreamLength());
        
        now[0] = 2000;
        db.setRetainDuration(5 * Clock.UNITS_PER_SEC);
        db.setReclaimInternalFraction(0.5);
        Assert.assertEquals("retain set", 5 * Clock.UNITS_PER_SEC, db.getRetainDuration());
        Assert.assertTrue("fraction set", db.getInternalFraction() == 0.5);
        Assert.assertTrue("written", db.getStreamLength() > length);
        db.stop();
    }
    
    /**
     * Bergdb 015-87: once the top node ordinals are used up to Db.LAST_TOP_ORDINAL, a setter
     * call that would write is refused as a user transaction is (bergdb 005-02), and
     * changes nothing; a call with the value in force writes nothing and is not refused.
     */
    @Nano private static void testReclaimSettingAtEndOfOrdinals() {
        MemoryStream s = new MemoryStream();
        CoreTestClock clock = new CoreTestClock();
        Db db = startOrdinalTest(s, clock, "sd1000", Db.LAST_TOP_ORDINAL - 10);
        int n = 0;
        while (db.internal().superRoot().topNodeId < Db.LAST_TOP_ORDINAL) {
            Assert.assertTrue("transactions " + n, n < 1000);
            clock.setTime(10L * (n + 1));
            db.execute(db.trans().put("/hot", "v" + n).build());
            n++;
        }
        final long length = db.getStreamLength();
        for (int i = 0; i < 2; i++) {
            String message = null;
            try {
                if (i == 0) db.setRetainDuration(5 * Clock.UNITS_PER_SEC);
                if (i == 1) db.setReclaimInternalFraction(0.5);
            } catch (DbException e) {
                message = e.getMessage();
            }
            Assert.assertTrue("refused " + i + ": " + message, message != null
                    && message.startsWith("The database has used its top node ordinals"));
        }
        Assert.assertEquals("retain unchanged", Long.MAX_VALUE, db.getRetainDuration());
        Assert.assertTrue("fraction unchanged", db.getInternalFraction() == 0.25);
        db.setRetainDuration(Long.MAX_VALUE);       // In force: not refused.
        db.setReclaimInternalFraction(0.25);
        Assert.assertEquals("nothing written", length, db.getStreamLength());
        Assert.assertEquals("super root", Db.LAST_TOP_ORDINAL,
                db.internal().superRoot().topNodeId);
        db.stop();
    }
    
    /** A builder with maximum node size 'size', 8, 14, 30 or 62. */
    private static DbBuilder nodeSize(DbBuilder b, int size) {
        switch (size) {
        case 8: return b.maxNodeSize8();
        case 14: return b.maxNodeSize14();
        case 30: return b.maxNodeSize30();
        case 62: return b.maxNodeSize62();
        default: throw new IllegalArgumentException("node size " + size);
        }
    }
    
    /** The bytes of a stream, from its first position. */
    private static byte[] bytesOf(MemoryStream s) throws IOException {
        byte[] bytes = new byte[(int) (s.getLength() - s.getFirstPos())];
        s.read(s.getFirstPos(), bytes, 0, bytes.length);
        return bytes;
    }
    
    /**
     * Bergdb 005-50: a start with another maximum node size than the database was created
     * with is refused, with a StreamFormatException that names both sizes, and writes
     * nothing; then a start with the database's size succeeds. Every pair of 8, 14, 30 and
     * 62, on a database as created, and on one of 300 transactions whose last record a crash
     * has torn, which recovery fills out. Before, the start reran the startup section with
     * the other size, and failed with "startup error, node ... not found", after recovery's
     * fill, or started.
     */
    @Nano
    private static void testOtherNodeSizeRefused() throws IOException {
        final int[] sizes = {8, 14, 30, 62};
        for (int a : sizes) {
            CoreTestClock clock = new CoreTestClock();
            MemoryStream created = new MemoryStream();
            Db db = nodeSize(Db.builder().testSetup(created).clock(clock), a).start();
            db.sync(SyncLevel.ORDINARY);
            db.close();
            
            MemoryStream torn = new MemoryStream();
            db = nodeSize(Db.builder().testSetup(torn).clock(clock), a).start();
            for (int i = 0; i < 300; i++) {
                clock.setTime(10 + i);
                db.execute(db.trans().put("key" + i, "value" + i));
            }
            db.sync(SyncLevel.ORDINARY);
            db.close();
            torn.truncate(torn.getLength() - 3);
            
            for (MemoryStream s : new MemoryStream[] {created, torn}) {
                for (int b : sizes) {
                    if (b == a) {
                        continue;
                    }
                    MemoryStream m = s.copy();
                    try {
                        nodeSize(Db.builder().testSetup(m).clock(clock), b).start();
                        throw new AssertionError("started with node size " + b
                                + ", created with " + a);
                    } catch (StreamFormatException e) {
                        Assert.assertEquals(StreamFormatException.class, e.getClass());
                        Assert.assertTrue(e.getMessage(), e.getMessage().contains(
                                "maximum node size is " + a + ", and this start uses " + b + "."));
                    }
                    Assert.assertArrayEquals("the stream as it was", bytesOf(s), bytesOf(m));
                }
                
                Db d = nodeSize(Db.builder().testSetup(s.copy()).clock(clock), a).start();
                if (s == torn) {
                    Assert.assertArrayEquals(StringUtil.toBytes("value298"),
                            DbUtil.get(d, Long.MAX_VALUE, "key298"));
                    Assert.assertNull(DbUtil.get(d, Long.MAX_VALUE, "key299"));     // Torn.
                }
                d.close();
            }
        }
    }
    
    /**
     * Bergdb 005-50: a database whose meta block has no maximum node size (0) is refused,
     * whatever size the start uses, and the start writes nothing: since bergdb 028-15 with a
     * StreamFormatException, as a damaged block, since every block of version 155 has the
     * size; until then with a VersioningStreamException, as a database written before
     * 2026-10-27.
     */
    @Nano
    private static void testNoNodeSizeRefused() throws IOException {
        CoreTestClock clock = new CoreTestClock();
        MemoryStream s = new MemoryStream();
        Db db = Db.builder().testSetup(s).clock(clock).start();
        clock.setTime(10);
        db.execute(db.trans().put("key1", "value1"));
        db.sync(SyncLevel.ORDINARY);
        db.close();
        Assert.assertTrue("one meta block", s.getLength() < RecoverableStream.META_BLOCK_DISTANCE);
        MemoryStream.TestAccess.write(s, new byte[2], 44);      // As before 005-50.
        
        for (int size : new int[] {8, 30}) {
            MemoryStream m = s.copy();
            try {
                nodeSize(Db.builder().testSetup(m).clock(clock), size).start();
                throw new AssertionError("started a database without a node size");
            } catch (StreamFormatException e) {
                Assert.assertFalse(e.toString(), e instanceof VersioningStreamException);
                Assert.assertTrue(e.getMessage(), e.getMessage().contains(
                        "maximum node size 0, none: the block is damaged"));
            }
            Assert.assertArrayEquals("the stream as it was", bytesOf(s), bytesOf(m));
        }
    }
    
    /**
     * Bergdb 024-19, Q6: 62 is the largest node size. A meta block that gives 63 or 126, which
     * no BergDB writes, is refused with a StreamFormatException that names the size and 62,
     * whatever size the start uses, and the start writes nothing. Before, the message named
     * DbBuilder.maxNodeSize126(), which does not exist.
     */
    @Nano
    private static void testNodeSizeAbove62Refused() throws IOException {
        CoreTestClock clock = new CoreTestClock();
        MemoryStream s = new MemoryStream();
        Db db = Db.builder().testSetup(s).clock(clock).start();
        clock.setTime(10);
        db.execute(db.trans().put("key1", "value1"));
        db.sync(SyncLevel.ORDINARY);
        db.close();
        Assert.assertTrue("one meta block", s.getLength() < RecoverableStream.META_BLOCK_DISTANCE);
        for (int bad : new int[] {63, 126}) {
            MemoryStream.TestAccess.write(s, new byte[] {(byte) bad, 0}, 44);   // u16, LE
            for (int size : new int[] {30, 62}) {
                MemoryStream m = s.copy();
                try {
                    nodeSize(Db.builder().testSetup(m).clock(clock), size).start();
                    throw new AssertionError("started a database of node size " + bad);
                } catch (StreamFormatException e) {
                    Assert.assertTrue(e.getMessage(), e.getMessage().contains(
                            "maximum node size " + bad + ", above 62, the largest"));
                }
                Assert.assertArrayEquals("the stream as it was", bytesOf(s), bytesOf(m));
            }
        }
    }
    
    /**
     * Bergdb 019-01: the version at offset 4 of a meta block is an int, and a block whose
     * bytes 6 or 7 are not 0 is refused with a VersioningStreamException, as a block of
     * another version is, and the start writes nothing. Every BergDB writes its version, 155
     * since bergdb 028-15, as an int there; until 2026-11-05 the version was read as 2 bytes,
     * and such a block was taken as version 154 (016-06, R6-F3).
     */
    @Nano
    private static void testVersionHighBytesRefused() throws IOException {
        CoreTestClock clock = new CoreTestClock();
        MemoryStream s = new MemoryStream();
        Db db = Db.builder().testSetup(s).clock(clock).start();
        clock.setTime(10);
        db.execute(db.trans().put("key1", "value1"));
        db.sync(SyncLevel.ORDINARY);
        db.close();
        Assert.assertTrue("one meta block", s.getLength() < RecoverableStream.META_BLOCK_DISTANCE);
        
        for (int offset : new int[] {6, 7}) {
            MemoryStream m = s.copy();
            MemoryStream.TestAccess.write(m, new byte[] {1}, offset);
            int version = 155 + (1 << (8 * (offset - 4)));
            try {
                Db.builder().testSetup(m).clock(clock).start().close();
                throw new AssertionError("started a database whose meta block has version "
                        + version + " (byte " + offset + " is 1)");
            } catch (VersioningStreamException e) {
                Assert.assertTrue(e.getMessage(), e.getMessage().contains("version " + version));
            }
            MemoryStream.TestAccess.write(m, new byte[] {0}, offset);
            Assert.assertArrayEquals("the stream as it was", bytesOf(s), bytesOf(m));
        }
        
        Db again = Db.builder().testSetup(s.copy()).clock(clock).start();
        try {
            Assert.assertEquals("value1", StringUtil.toString(DbUtil.get(again, Long.MAX_VALUE,
                    "key1")));
        } finally {
            again.close();
        }
    }
    
    /** Simplest possible delete-and-restart test. */
    @Nano private static void testDelete1() {
        MemoryStream s = new MemoryStream();
        CoreTestClock clock = new CoreTestClock();
        Db db = Db.builder().testSetup(s).clock(clock).start();
        
        clock.setTime(10);
        db.execute(db.trans().put("k1", "k1-value"));
        
        clock.setTime(20);
        db.execute(db.trans().delete("k1"));
        db.sync(SyncLevel.ORDINARY);
        
        //db.printGraph(System.out);
        //db.getStream().print(System.out);
        
        db.close();
        
        // Restart
        
        Db db2 = Db.builder().testSetup(s.copy()).start();
        //db2.printGraph(System.out);
        
        byte[] v1 = DbUtil.get(db2, 15, "k1");
        Assert.assertArrayEquals(StringUtil.toBytes("k1-value"), v1);
        v1 = DbUtil.get(db2, 25, "k1");
        Assert.assertNull(v1);
        db2.close();
    }
    
    /** Multiple deletes in a single transaction. */
    @Nano private static void testDelete2() {
        MemoryStream s = new MemoryStream();
        CoreTestClock clock = new CoreTestClock();
        Db db = Db.builder().testSetup(s).clock(clock).start();
        
        clock.setTime(10);
        db.execute(db.trans().put("k1", "k1-value").put("k2", "k2-value"));
        
        clock.setTime(20);
        db.execute(db.trans().delete("k1").delete("k2").delete("kk").put("k3", "k3-value").build());
        
        long sum1 = DbUtil.checksum(db);
        db.sync(SyncLevel.ORDINARY);
        db.close();
        
        // Restart
        
        Db db2 = Db.builder().testSetup(s.copy()).start();        
        long sum2 = DbUtil.checksum(db2);
        
        Assert.assertEquals(sum1, sum2);
        db2.close();
    }

    /**
     * Deletes of missing keys of 7 bytes or more (more than one key segment), then two
     * restarts. Regression test for a bug found 2026-10-12: the delete created
     * a key node for a missing segment, the rerun at startup did not, so node ids
     * differed after the first restart, and the second restart failed.
     */
    @Nano private static void testDeleteMissingLongKey() {
        MemoryStream s = new MemoryStream();
        CoreTestClock clock = new CoreTestClock();
        Db db = Db.builder().testSetup(s).clock(clock).start();

        clock.setTime(10);
        db.execute(db.trans().put("/a", "a-value").put("/abcdefXX", "x-value"));

        clock.setTime(20);
        db.execute(db.trans().delete("/k/1000"));            // two segments, both missing

        clock.setTime(30);
        db.execute(db.trans().delete("/abcdefgh12345"));     // three segments, first exists

        clock.setTime(40);
        db.execute(db.trans().put("/b", "b-value"));
        long sum1 = DbUtil.checksum(db);
        db.sync(SyncLevel.ORDINARY);
        db.stop();

        // Restart, put, restart

        s = s.copy();
        db = Db.builder().testSetup(s).clock(clock).start();
        Assert.assertEquals("checksum after first restart", sum1, DbUtil.checksum(db));

        clock.setTime(50);
        db.execute(db.trans().put("/c", "c-value"));
        long sum2 = DbUtil.checksum(db);
        db.sync(SyncLevel.ORDINARY);
        db.stop();

        s = s.copy();
        db = Db.builder().testSetup(s).clock(clock).start();
        Assert.assertEquals("checksum after second restart", sum2, DbUtil.checksum(db));
        Assert.assertEquals("a-value", DbUtil.getString(db, "/a"));
        Assert.assertEquals("x-value", DbUtil.getString(db, "/abcdefXX"));
        Assert.assertEquals("c-value", DbUtil.getString(db, "/c"));
        Assert.assertNull(DbUtil.get(db, Long.MAX_VALUE, "/k/1000"));
        db.stop();
    }
    
    /**
     * One object per node after restarts with bounded startup (level 2): every node in D
     * is the node table's object for its id and is dirty, every dirty node in memory is
     * in D, and no id has two dirty objects. Regression test for bugs found 2026-10-12
     * (level 2): after a
     * restart, D could hold a copy of a node read from the stream while the Dag held
     * another object with the same id; and Db and NodeCollection had a node table each.
     */
    @Nano private static void testOneObjectPerNodeAfterRestarts() {
        Random rnd = new Random(1);
        MemoryStream s = new MemoryStream();
        CoreTestClock clock = new CoreTestClock();
        Db db = Db.builder().testSetup(s).clock(clock).startupDistance(10 * 1000).start();
        long time = 10;
        int restarts = 0;
        
        for (int i = 0; i < 1000; i++) {
            clock.setTime(time += 10);
            Trans.Builder b = db.trans();
            Set<String> keys = new LinkedHashSet<String>();
            int ops = 1 + rnd.nextInt(3);
            while (keys.size() < ops) {
                keys.add("/k/" + rnd.nextInt(500));
            }
            for (String key : keys) {
                byte[] value = new byte[1 + rnd.nextInt(40)];
                rnd.nextBytes(value);
                b.put(key, value);
            }
            db.execute(b.build());
            
            if (i % 250 == 249) {
                db.sync(SyncLevel.ORDINARY);
                db.stop();
                s = s.copy();
                db = Db.builder().testSetup(s).clock(clock).start();
                restarts++;
            }
            
            if (restarts > 0 && i % 250 < 20) {
                String problems = identityViolations(db);
                Assert.assertTrue("transaction " + i + ": " + problems, problems == null);
            }
        }
        
        Assert.assertTrue("startup pos moved", db.internal().x().startupPos.get() 
                > RecoverableStream.META_BLOCK_SIZE);
        db.close();
    }
    
    /**
     * Checks one object per node: returns null if OK, else a description. See
     * testOneObjectPerNodeAfterRestarts().
     */
    static String identityViolations(Db db) {
        final Cache3 table = db.internal().cache();
        final Set<Node> inD = Collections.newSetFromMap(new IdentityHashMap<Node, Boolean>());
        final StringBuilder problems = new StringBuilder();
        
        db.internal().transSeq().visitGotDirtyNodes(Long.MAX_VALUE, new TransSeq.NodeVisitor() {
            public void node(Node node, long tpos, long lastTpos) {
                inD.add(node);
                if (table.getNode(node.getId()) != node) {
                    problems.append("node " + node.getId() + " in D is not in the node table; ");
                }
                if (!node.isDirty()) {
                    problems.append("node " + node.getId() + " in D is not dirty; ");
                }
            }
        });
        
        final Map<Long, Node> dirtyById = new HashMap<Long, Node>();
        db.internal().dag().visitMemoryNodes(new NodeVisitor() {
            public void visit(TopNode node) { check(node); }
            public void visit(KeyNode node) { check(node); }
            public void visit(ValueNode node) {}
            
            private void check(Node node) {
                if (!node.isDirty()) {
                    return;
                }
                if (!inD.contains(node)) {
                    problems.append("dirty node " + node.getId() + " is not in D; ");
                }
                Node other = dirtyById.put(node.getId(), node);
                if (other != null && other != node) {
                    problems.append("two dirty objects for node " + node.getId() + "; ");
                }
            }
        });
        
        return problems.length() == 0 ? null : problems.toString();
    }
    
    /**
     * Level 2, restarts with bounded startup: puts, deletes, short and long keys, and
     * transactions with one to twenty keys; after each restart, every key is checked at
     * the latest time and at earlier times. See bergdb 027-01, levels.md.
     * Fails without DbStarter.canonicalNode()'s use of the stored position (a delete of
     * a key that does not exist). Larger: testLevel2RestartsKeepAllValuesF.
     */
    @Nano private static void testLevel2RestartsKeepAllValues() {
        checkAllValues(1, 30, 50, 200);
        checkAllValues(2, 8, 25, 200);
    }
    
    @Nano("f") private static void testLevel2RestartsKeepAllValuesF() {
        checkAllValues(1, 30, 50, 1000);
        checkAllValues(2, 8, 25, 1000);
    }
    
    private static void checkAllValues(long seed, int maxNodeSize, int restartEvery, int n) {
        Level2Run run = new Level2Run(seed, maxNodeSize, restartEvery);
        run.run(n);
        Assert.assertTrue(run.problem, run.problem == null);
    }
    
    /**
     * Level 2: the stream with restarts is the same, byte for byte, as without (T2 in
     * bergdb 027-01, sis-model.md). Fails without NodeCollection.resolvePointers().
     * Larger: testLevel2SameStreamWithRestartsF.
     */
    @Nano private static void testLevel2SameStreamWithRestarts() throws java.io.IOException {
        checkSameStream(2, 30, 20, 200);
    }
    
    @Nano("f") private static void testLevel2SameStreamWithRestartsF() throws java.io.IOException {
        checkSameStream(3, 30, 40, 600);
    }
    
    private static void checkSameStream(long seed, int maxNodeSize, int restartEvery, int n) 
            throws java.io.IOException {
        Level2Run a = new Level2Run(seed, maxNodeSize, 0);
        a.run(n);
        Level2Run b = new Level2Run(seed, maxNodeSize, restartEvery);
        b.run(n);
        Assert.assertTrue(b.problem, b.problem == null);
        
        long length = a.stream.getLength();
        Assert.assertEquals("stream length", length, b.stream.getLength());
        byte[] bytesA = new byte[(int) length];
        byte[] bytesB = new byte[(int) length];
        a.stream.read(0, bytesA, 0, (int) length);
        b.stream.read(0, bytesB, 0, (int) length);
        int first = -1;
        for (int i = 0; i < length && first < 0; i++) {
            if (bytesA[i] != bytesB[i]) {
                first = i;
            }
        }
        Assert.assertEquals("first byte that differs", -1, first);
    }
    
    /**
     * After a decrease of the startup distance (bergdb 007-03, D4; 007-07) the deadline is
     * at the span of the section's transactions, which a start rebuilds, and the new
     * setting is in the meta block that setStartupDistance's transaction writes: the stream
     * with restarts while the section comes down, one right after the call, is the same,
     * byte for byte, as without (010, P2).
     */
    @Nano("f") private static void testSameStreamAfterDecreaseWithRestartsF() 
            throws IOException {
        MemoryStream a = decreaseRun(0);
        MemoryStream b = decreaseRun(10);
        long length = a.getLength();
        Assert.assertEquals("stream length", length, b.getLength());
        byte[] bytesA = new byte[(int) length];
        byte[] bytesB = new byte[(int) length];
        a.read(0, bytesA, 0, (int) length);
        b.read(0, bytesB, 0, (int) length);
        Assert.assertTrue("same stream", java.util.Arrays.equals(bytesA, bytesB));
    }
    
    /**
     * Puts of 1 kB at a startup distance of 2 MB, lowered to 500 kB after 4000 of them, and
     * 300 more, with a restart every restartEvery after the decrease (0 for none) and one
     * right after it; the stream.
     */
    private static MemoryStream decreaseRun(int restartEvery) {
        MemoryStream stream = new MemoryStream();
        CoreTestClock clock = new CoreTestClock();
        Db db = Db.builder().testSetup(stream).clock(clock).startupDistance(2000 * 1000).start();
        Random random = new Random(1);
        long time = 10;
        for (int i = 0; i < 4300; i++) {
            boolean restart = restartEvery > 0 && i > 4000 && i % restartEvery == 0;
            if (i == 4000) {
                db.setStartupDistance(500 * 1000);
                restart = restartEvery > 0;
            }
            if (restart) {
                db.sync(SyncLevel.ORDINARY);
                db.close();
                stream = stream.copy();     // db.close() closed it
                db = Db.builder().testSetup(stream).clock(clock).start();
            }
            clock.setTime(time++);
            byte[] value = new byte[1000];
            random.nextBytes(value);
            db.execute(db.trans().put("/k/" + random.nextInt(1000), value).build());
        }
        db.sync(SyncLevel.ORDINARY);
        db.close();
        return stream;
    }
    
    /**
     * A random run with restarts every restartEvery transactions (0 for none), and with
     * lookups of every key after each restart (or at the same points, if lookupEvery).
     */
    static class Level2Run {
        final Random rnd;
        final Random lookupRnd;
        final int maxNodeSize;
        final int restartEvery;
        int lookupEvery;
        boolean doRestarts = true;
        final CoreTestClock clock = new CoreTestClock();
        final Map<String, TreeMap<Long, byte[]>> model = new HashMap<String, TreeMap<Long, byte[]>>();
        final List<Long> times = new ArrayList<Long>();
        MemoryStream stream = new MemoryStream();
        Db db;
        String problem;
        
        Level2Run(long seed, int maxNodeSize, int restartEvery) {
            this.rnd = new Random(seed);
            this.lookupRnd = new Random(seed + 1000);
            this.maxNodeSize = maxNodeSize;
            this.restartEvery = restartEvery;
            this.lookupEvery = restartEvery;
        }
        
        Db start() {
            DbBuilder b = Db.builder().testSetup(stream).clock(clock).startupDistance(2000);
            if (maxNodeSize == 8) b.maxNodeSize8();
            if (maxNodeSize == 30) b.maxNodeSize30();
            return b.start();
        }
        
        void run(int n) {
            db = start();
            long time = 10;
            
            for (int i = 0; i < n && problem == null; i++) {
                clock.setTime(time += 10);
                times.add(time);
                Trans.Builder b = db.trans();
                Set<String> keys = new LinkedHashSet<String>();
                int ops = rnd.nextInt(10) == 0 ? 1 + rnd.nextInt(20) : 1 + rnd.nextInt(3);
                while (keys.size() < ops) {
                    keys.add(rnd.nextBoolean() ? "/k/" + rnd.nextInt(300) : "/long/" + rnd.nextInt(300));
                }
                for (String key : keys) {
                    byte[] value = null;
                    if (rnd.nextInt(5) == 0) {
                        b.delete(key);
                    } else {
                        value = new byte[1 + rnd.nextInt(60)];
                        rnd.nextBytes(value);
                        b.put(key, value);
                    }
                    TreeMap<Long, byte[]> history = model.get(key);
                    if (history == null) {
                        model.put(key, history = new TreeMap<Long, byte[]>());
                    }
                    history.put(time, value);
                }
                db.execute(b.build());
                
                if (doRestarts && restartEvery > 0 && i % restartEvery == restartEvery - 1) {
                    db.sync(SyncLevel.ORDINARY);
                    db.stop();
                    stream = stream.copy();
                    try {
                        db = start();
                    } catch (RuntimeException e) {
                        problem = "restart after transaction " + i + ": " + e;
                        return;
                    }
                }
                
                if (lookupEvery > 0 && i % lookupEvery == lookupEvery - 1) {
                    check(i);
                }
            }
            
            db.sync(SyncLevel.ORDINARY);
            db.close();
        }
        
        /** Checks every key at the latest time and at ten earlier times. */
        void check(int i) {
            List<Long> lookupTimes = new ArrayList<Long>();
            lookupTimes.add(Long.MAX_VALUE);
            for (int j = 0; j < 10; j++) {
                lookupTimes.add(times.get(lookupRnd.nextInt(times.size())) 
                        + lookupRnd.nextInt(2) - 1);
            }
            
            for (Map.Entry<String, TreeMap<Long, byte[]>> e : model.entrySet()) {
                for (long t : lookupTimes) {
                    Map.Entry<Long, byte[]> expected = e.getValue().floorEntry(t);
                    byte[] expectedValue = expected == null ? null : expected.getValue();
                    byte[] value;
                    try {
                        value = DbUtil.get(db, t, e.getKey());
                    } catch (RuntimeException ex) {
                        problem = "after restart at " + i + ": get(" + e.getKey() + ", " + t 
                                + ") failed: " + ex;
                        return;
                    }
                    if (!java.util.Arrays.equals(expectedValue, value)) {
                        problem = "after restart at " + i + ": " + e.getKey() + " at time " + t
                                + ": expected " + (expectedValue == null ? "none" 
                                        : expectedValue.length + " bytes") 
                                + ", got " + (value == null ? "none" : value.length + " bytes");
                        return;
                    }
                }
            }
        }
    }
    
    /**
     * After a restart, the meta block knows the position of the last transaction, as
     * without the restart, so that the next meta block written is the same. Regression 
     * test for a bug found 2026-10-12 (level 2, step 3): it kept the position 
     * stored in the last meta block on disk, from before the transactions after it.
     */
    @Nano private static void testLastTransPosAfterRestart() {
        MemoryStream s = new MemoryStream();
        CoreTestClock clock = new CoreTestClock();
        Db db = Db.builder().testSetup(s).clock(clock).start();
        long lastTpos = -1;
        for (int i = 0; i < 10; i++) {
            clock.setTime(10 + 10 * i);
            Trans t = db.trans().put("/k/" + i, "value").build();
            db.execute(t);
            lastTpos = t.tpos;
        }
        Assert.assertEquals("before restart", lastTpos, 
                db.internal().nodeStream().getMetaBlock().getLastTransSpos());
        db.sync(SyncLevel.ORDINARY);
        db.stop();
        
        db = Db.builder().testSetup(s.copy()).clock(clock).start();
        Assert.assertEquals("after restart", lastTpos, 
                db.internal().nodeStream().getMetaBlock().getLastTransSpos());
        db.close();
    }
    
    /**
     * Transactions that change nothing do not mark the super root; enough of them move the
     * startup pos past every top node version. Startup must still find the super root, from
     * the last transaction's topPos. Regression test for M18 of bergdb 011-11,
     * found 2026-10-15: the database could not start ("Could not find super node in startup
     * section").
     */
    @Nano private static void testRestartAfterTransactionsThatChangeNothing() {
        for (int mode = 0; mode < 2; mode++) {      // 0: no KVs, 1: deletes of missing keys
            MemoryStream s = new MemoryStream();
            CoreTestClock clock = new CoreTestClock();
            Db db = Db.builder().testSetup(s).clock(clock).startupDistance(100).maxNodeSize8()
                    .start();
            long time = 10;
            for (int i = 0; i < 50; i++) {
                clock.setTime(time++);
                db.execute(db.trans().put("/k/" + i, "v" + i).build());
            }
            for (int round = 0; round < 3; round++) {
                for (int i = 0; i < 40; i++) {
                    clock.setTime(time++);
                    Trans.Builder b = db.trans();
                    if (mode == 1) b.delete("/missing/" + round + "/" + i);
                    db.execute(b.build());
                }
                db.sync(SyncLevel.ORDINARY);
                db.stop();
                s = s.copy();
                db = Db.builder().testSetup(s).clock(clock).startupDistance(100).maxNodeSize8()
                        .start();
                for (int i = 0; i < 50; i++) {
                    Assert.assertArrayEquals("mode " + mode + ", round " + round + ", key " + i,
                            StringUtil.toBytes("v" + i), DbUtil.get(db, Long.MAX_VALUE, "/k/" + i));
                }
                clock.setTime(time++);
                db.execute(db.trans().put("/k/" + round, "v" + round).build());
            }
            db.close();
        }
    }

    /**
     * A database with more than 32,768 top nodes restarts with its history (2026-10-16, bergdb
     * item 001, WP A3; review-13-claude, section 2, of F1-008-13). One key updated in every
     * transaction, at node size 8, makes a new top node about every four transactions, so
     * about 131,000 transactions pass ordinal 32,768. Before the fix of
     * StoredTopNode.toLongs, the restart failed ("Bad TopNode ID of TopNode in stream"). An
     * f-test: about 1.4 s.
     */
    @Nano("f") private static void testRestartAfterManyTopNodes() {
        MemoryStream s = new MemoryStream();
        CoreTestClock clock = new CoreTestClock();
        Db db = Db.builder().testSetup(s).clock(clock).startupDistance(10000).maxNodeSize8()
                .start();
        int n = 0;
        while (db.internal().newestWrittenTop().topNodeId < 32800) {
            clock.setTime(10L * (n + 1));
            db.execute(db.trans().put("/hot", "v" + n).build());
            n++;
        }
        long superRoot = db.internal().superRoot().topNodeId;
        db.sync(SyncLevel.ORDINARY);
        db.stop();
        s = s.copy();
        db = Db.builder().testSetup(s).clock(clock).startupDistance(10000).maxNodeSize8().start();
        Assert.assertEquals("super root after the restart", superRoot,
                db.internal().superRoot().topNodeId);
        int[] at = {0, 1, n / 4, n / 2, (3 * n) / 4, n - 2, n - 1};
        for (int j : at) {
            Assert.assertArrayEquals("value at the time of transaction " + j,
                    StringUtil.toBytes("v" + j), DbUtil.get(db, 10L * (j + 1), "/hot"));
        }
        while (db.internal().superRoot().topNodeId == superRoot) {
            clock.setTime(10L * (n + 1));
            db.execute(db.trans().put("/hot", "v" + n).build());
            n++;
        }
        Assert.assertEquals("the next top node", superRoot + 1, db.internal().superRoot().topNodeId);
        db.close();
    }

    /**
     * Databases cross the top node ordinals 2^30, 2^31, 2^32 and 2^47, and restart with their
     * history (bergdb item 005-02, register M46). Until then the ordinal was an int below 2^30,
     * and at that bound TopNode threw in the middle of a root split (bergdb item 002, 002-02,
     * section 2). The second top node starts 20 below the boundary (DbBuilder.secondTopOrdinal);
     * one key updated in every transaction, at node size 8, makes a new top node about every
     * four transactions. Three setups: a startup distance of 1,000 bytes, so that the restart
     * reads top nodes above the boundary from the stream; 100,000 bytes, so that the restart
     * makes them all again; and 1,000 bytes with every evictable object evicted after every
     * transaction, so that lookups load top nodes. Every historical value is checked before
     * and after the restart, and the next top node continues the ordinals.
     */
    @Nano private static void testOrdinalsAcrossBoundaries() {
        long[] boundaries = {1L << 30, 1L << 31, 1L << 32, 1L << 47};
        String[] setups = {"sd1000", "sd100000", "evict"};
        for (long boundary : boundaries) {
            for (String setup : setups) {
                String what = "boundary " + boundary + ", " + setup;
                MemoryStream s = new MemoryStream();
                CoreTestClock clock = new CoreTestClock();
                Db db = startOrdinalTest(s, clock, setup, boundary - 20);
                int n = 0;
                while (db.internal().superRoot().topNodeId < boundary + 20) {
                    Assert.assertTrue(what + ", transactions " + n, n < 1000);
                    clock.setTime(10L * (n + 1));
                    db.execute(db.trans().put("/hot", "v" + n).build());
                    n++;
                }
                if (!setup.equals("sd100000")) {
                    Assert.assertTrue(what + ", a top node above the boundary written",
                            db.internal().newestWrittenTop().topNodeId >= boundary);
                }
                checkHotHistory(db, n, what + ", before the restart");
                long superRoot = db.internal().superRoot().topNodeId;
                db.sync(SyncLevel.ORDINARY);
                db.stop();
                s = s.copy();
                db = startOrdinalTest(s, clock, setup, boundary - 20);
                Assert.assertEquals(what + ", super root after the restart", superRoot,
                        db.internal().superRoot().topNodeId);
                checkHotHistory(db, n, what + ", after the restart");
                while (db.internal().superRoot().topNodeId == superRoot) {
                    clock.setTime(10L * (n + 1));
                    db.execute(db.trans().put("/hot", "v" + n).build());
                    n++;
                }
                Assert.assertEquals(what + ", the next top node", superRoot + 1,
                        db.internal().superRoot().topNodeId);
                checkHotHistory(db, n, what + ", at the end");
                db.stop();
            }
        }
    }

    /**
     * The end of the top node ordinals (bergdb item 005-02): once the super root's ordinal is
     * Db.LAST_TOP_ORDINAL, 1,024 below the bound, 2^48 - 1, a user transaction is refused
     * before it changes anything. The keys keep their values, no node is left in the writer's
     * list, the history is right, and the database restarts and refuses again. An internal
     * transaction is not refused: reclaim runs its transactions after a user transaction has
     * committed, in the margin below the bound.
     */
    @Nano private static void testEndOfOrdinals() {
        MemoryStream s = new MemoryStream();
        CoreTestClock clock = new CoreTestClock();
        Db db = startOrdinalTest(s, clock, "sd1000", Db.LAST_TOP_ORDINAL - 10);
        int n = 0;
        while (db.internal().superRoot().topNodeId < Db.LAST_TOP_ORDINAL) {
            Assert.assertTrue("transactions " + n, n < 1000);
            clock.setTime(10L * (n + 1));
            db.execute(db.trans().put("/hot", "v" + n).build());
            n++;
        }
        for (int round = 0; round < 2; round++) {
            String what = round == 0 ? "before the restart" : "after the restart";
            assertRefused(db, db.trans().put("/hot", "x").build(), what);
            assertRefused(db, db.trans().put("/other", "x").put("/hot", "x").build(), what);
            Assert.assertEquals(what + ", super root", Db.LAST_TOP_ORDINAL,
                    db.internal().superRoot().topNodeId);
            Assert.assertEquals(what + ", nodes in the writer's list", 0,
                    db.internal().x().transNodes.size());
            Assert.assertTrue(what + ", /other", DbUtil.get(db, Long.MAX_VALUE, "/other") == null);
            Assert.assertArrayEquals(what + ", /hot", StringUtil.toBytes("v" + (n - 1)),
                    DbUtil.get(db, Long.MAX_VALUE, "/hot"));
            checkHotHistory(db, n, what);
            db.sync(SyncLevel.ORDINARY);
            db.stop();
            s = s.copy();
            db = startOrdinalTest(s, clock, "sd1000", Db.LAST_TOP_ORDINAL - 10);
        }
        clock.setTime(10L * (n + 1));
        Trans internal = db.trans().put("/internal", "i").build();
        internal.isInternal = true;
        db.execute(internal);
        Assert.assertArrayEquals("an internal transaction", StringUtil.toBytes("i"),
                DbUtil.get(db, Long.MAX_VALUE, "/internal"));
        assertRefused(db, db.trans().put("/hot", "x").build(), "after an internal transaction");
        db.stop();
    }

    /**
     * Top node ordinals across 2^32, and to the end, with reclaim (bergdb item 005-02). One
     * key updated in every transaction and one written in the first only, which reclaim
     * rewrites; a new top node about every nine transactions (every three until bergdb
     * 028-15, when every database got the startup distance's KV: from 400 below 2^32 and
     * the end then, from 150 now). A retention of one second
     * cuts the front of the stream, from about transaction 900 on, with the first top node
     * and the second, whose skip pointers name the first. A restart every 150 transactions;
     * after each, both keys are checked at every transaction's time from the first available
     * time on. Near the end, reclaim's internal transactions are not refused; their top nodes
     * stay within Db.TOP_ORDINAL_MARGIN, at most five above Db.LAST_TOP_ORDINAL.
     */
    @Nano private static void testOrdinalsWithReclaim() {
        runOrdinalsWithReclaim((1L << 32) - 150, (1L << 32) + 100);
        runOrdinalsWithReclaim(Db.LAST_TOP_ORDINAL - 150, Long.MAX_VALUE);
    }

    /** Runs until the super root's ordinal is 'until' or a transaction is refused. */
    private static void runOrdinalsWithReclaim(long second, long until) {
        String what = "second ordinal " + second;
        CoreTestClock clock = new CoreTestClock();
        long time = Clock.UNITS_PER_SEC;
        clock.setTime(time);
        CutStream s = new CutStream();
        Db db = startReclaimOrdinalTest(s, clock, second);
        Map<String, TreeMap<Long, String>> model = new HashMap<String, TreeMap<Long, String>>();
        List<Long> times = new ArrayList<Long>();
        long secondTime = -1;       // the time of the transaction that made the second top node
        boolean refused = false;
        for (int i = 0; !refused && db.internal().superRoot().topNodeId < until; i++) {
            Assert.assertTrue(what + ", transactions " + i, i < 5000);
            time += Clock.UNITS_PER_SEC / 20;
            clock.setTime(time);
            String v = "v" + i;
            Trans.Builder b = db.trans().put("/hot", v);
            if (i == 0) {
                b.put("/cold", v);
            }
            try {
                db.execute(b.build());
            } catch (DbException e) {
                Assert.assertTrue(what + ", " + e.getMessage(), until == Long.MAX_VALUE
                        && db.internal().superRoot().topNodeId >= Db.LAST_TOP_ORDINAL);
                refused = true;
                continue;
            }
            modelPut(model, "/hot", time, v);
            if (i == 0) {
                modelPut(model, "/cold", time, v);
            }
            times.add(time);
            if (secondTime == -1 && db.internal().superRoot().topNodeId >= second) {
                secondTime = time;
            }
            if (i % 150 == 149) {
                db.sync(SyncLevel.ORDINARY);
                db.stop();
                s = s.copy();
                db = startReclaimOrdinalTest(s, clock, second);
                checkModel(db, model, times, what + ", after the restart at transaction " + i);
            }
        }
        Assert.assertTrue(what + ", a cut", s.getCut() > 0);
        Assert.assertTrue(what + ", the second top node cut away: first available time "
                + db.getFirstAvailableLookupTime() + ", the second's " + secondTime,
                secondTime != -1 && db.getFirstAvailableLookupTime() > secondTime);
        long superRoot = db.internal().superRoot().topNodeId;
        if (until == Long.MAX_VALUE) {
            Assert.assertTrue(what + ", refused", refused);
            Assert.assertTrue(what + ", super root " + superRoot, superRoot >= Db.LAST_TOP_ORDINAL
                    && superRoot <= Db.LAST_TOP_ORDINAL + 5);
            assertRefused(db, db.trans().put("/hot", "x").build(), what);
        }
        checkModel(db, model, times, what + ", at the end");
        db.sync(SyncLevel.ORDINARY);
        db.stop();
        db = startReclaimOrdinalTest(s.copy(), clock, second);
        Assert.assertEquals(what + ", super root after the last restart", superRoot,
                db.internal().superRoot().topNodeId);
        checkModel(db, model, times, what + ", after the last restart");
        if (until == Long.MAX_VALUE) {
            assertRefused(db, db.trans().put("/hot", "x").build(),
                    what + ", after the last restart");
        }
        db.stop();
    }

    private static Db startOrdinalTest(AppendOnlyStream s, CoreTestClock clock, String setup,
            long second) {
        DbBuilder b = Db.builder().testSetup(s).clock(clock).maxNodeSize8()
                .startupDistance(setup.equals("sd100000") ? 100000 : 1000)
                .secondTopOrdinal(second);
        if (setup.equals("evict")) {
            b.evictionSchedule(Eviction.Schedule.EVERY, 1).audit(1);
        }
        return b.start();
    }

    /** As Reclaim.Tester's databases for cuts. */
    private static Db startReclaimOrdinalTest(CutStream s, CoreTestClock clock, long second) {
        Db db = Db.builder().testSetup(s).clock(clock).maxNodeSize8().startupDistance(2000)
                .secondTopOrdinal(second).start();
        db.setRetainDuration(1 * Clock.UNITS_PER_SEC);
        return db;
    }

    /** "/hot" at the time of each of the n transactions, 10 * (k + 1), is "v" + k. */
    private static void checkHotHistory(Db db, int n, String what) {
        for (int k = 0; k < n; k++) {
            Assert.assertArrayEquals(what + ", the value at the time of transaction " + k,
                    StringUtil.toBytes("v" + k), DbUtil.get(db, 10L * (k + 1), "/hot"));
        }
    }

    private static void assertRefused(Db db, Trans t, String what) {
        String message = null;
        try {
            db.execute(t);
        } catch (DbException e) {
            message = e.getMessage();
        }
        Assert.assertTrue(what + ", refused: " + message, message != null
                && message.startsWith("The database has used its top node ordinals"));
    }

    private static void modelPut(Map<String, TreeMap<Long, String>> model, String key, long time,
            String value) {
        TreeMap<Long, String> m = model.get(key);
        if (m == null) {
            m = new TreeMap<Long, String>();
            model.put(key, m);
        }
        m.put(time, value);
    }

    /** Every key at every transaction's time from the first available time on. */
    private static void checkModel(Db db, Map<String, TreeMap<Long, String>> model,
            List<Long> times, String what) {
        long first = db.getFirstAvailableLookupTime();
        for (long t : times) {
            if (t < first) {
                continue;
            }
            for (Map.Entry<String, TreeMap<Long, String>> e : model.entrySet()) {
                Map.Entry<Long, String> v = e.getValue().floorEntry(t);
                Assert.assertArrayEquals(what + ", " + e.getKey() + " at " + t,
                        v == null ? null : StringUtil.toBytes(v.getValue()),
                        DbUtil.get(db, t, e.getKey()));
            }
        }
    }
}
