package bergdb.storage;

import bergdb.common.Bytes;
import bergdb.common.Util;
import bergdb.nanotest.Assert;
import bergdb.nanotest.Nano;

/**
 * An instance of this class represents a meta information block in the 
 * db stream (RecoverableStream). The meta information includes 
 * the spos of the last successful transaction.
 * Little-endian-first byte order is used.
 *
 * <pre>
 * FORMAT OF A META BLOCK, v155
 * Offset  Size    Description
 * 0       4       Magic bytes, meta block signature. Always the bytes for ASCII "berg".
 * 4       4       Version of BergDB stream format, an int (155 for this version; 154 until
 *                 release 2026.5, bergdb 028-15). Until 2026-11-05 it was read as an
 *                 unsigned short, so bytes 6 and 7 were not checked; every version of BergDB
 *                 writes 0 there (bergdb 019-01).
 * 8       8       time, the creation's time as a long, set once (Db.writePrimordialTransaction).
 * 16      8       lastTrans, spos of last valid transaction completely written
 *                 before the meta block.
 * 24     16       Database ID. 128 random bits, used as unique database ID.
 * 40      4       Reserved, written zero and not read. The startup distance until version
 *                 155; since then an internal KV of the Core (bergdb 028-15, Db.SD_KEY).
 * 44      2       maxNodeSize, the maximum node size of the database, an unsigned short:
 *                 30 in every database a user makes (bergdb 026-08), 8, 14 or 62 in some
 *                 that BergDB's own tests make; a start with another size is refused, and
 *                 so is 0, a damaged block (bergdb 005-50; every block of version 155 has
 *                 the size).
 * 46     81       Reserved, must be set to zero.
 * 127     1       META_BLOCK_LAST_BYTE, 10. It indicates that the block is valid.
 * </pre>
 */
public class MetaBlock {    
    private static final byte META_BLOCK_LAST_BYTE = (byte) Util.identity(10);
    public static final byte[] MAGIC = new byte[] {'b', 'e', 'r', 'g'};
    
    /** The version of release 2026.5 and earlier: the startup distance at offset 40. */
    public static final int VERSION_154 = Util.identity(154);
    
    /** The version since release 2026.6 (bergdb 028-15): offset 40 reserved. */
    public static final int VERSION_155 = Util.identity(155);
    
    /**
     * The version of the stream's framing, which RecoverableStream reads and writes: the meta
     * blocks (their size, distance and layout) and a record's size field and last byte. A
     * change of these changes this number, which recovery checks in each meta block it reads,
     * before it writes anything (2026-10-25, bergdb 005-40). What a record holds has a
     * version of its own, StoredTrans.RECORD_FORMAT. New databases only: a stream of another
     * version is refused. A new field in the reserved bytes, which an older version can
     * ignore, keeps the number, as maxNodeSize at offset 44 did (2026-10-27, bergdb 005-50):
     * an older version neither checks nor reads those bytes, and it copies a block it read
     * whole, so it starts such a stream as before and passes the field on. 155 since
     * 2026-11-18 (bergdb 028-15, option A): the startup distance left the block for an
     * internal KV of the Core, which an older version does not read; 2026.6 refuses 154,
     * which every release until 2026.5 wrote, and 2026.5 refuses 155, both before they
     * write (the rule of bergdb 026-12, SF3).
     */
    static final int CURRENT_VERSION = VERSION_155;
    
    /** Bytes to fill-out meta block in case of a stream crash in meta block. */
    static final byte[] FILL_OUT_TEMPLATE = new byte[RecoverableStream.META_BLOCK_SIZE];
    
    static {
        System.arraycopy(MAGIC, 0, FILL_OUT_TEMPLATE, 0, 4);
        Bytes.intToBytesLE(CURRENT_VERSION, FILL_OUT_TEMPLATE, 4);
    }
    
    private byte[] block;
    private long pos;         // stream pos, only used sometimes
    
    /**
     * Creates a new MetaBlock with lastTrans -1: no record yet.
     */
    public MetaBlock() {
        pos = -1;
        block = new byte[RecoverableStream.META_BLOCK_SIZE];
        initBlock();
    }

    private void initBlock() {
        System.arraycopy(MAGIC, 0, block, 0, 4);
        Bytes.intToBytesLE(CURRENT_VERSION, block, 4);
        
        block[RecoverableStream.META_BLOCK_SIZE - 1] = META_BLOCK_LAST_BYTE;
            // last byte set to indicate successful meta block
        setLastTransSpos(Constants.SposNULL);
    }
    
    /**
     * Creates a new MetaBlock given the 'block' byte buffer.
     * 
     * @param block  The bytes of the meta block. Must be of length RecoverableStream.META_BLOCK_SIZE.
     */ 
    MetaBlock(byte[] block, long pos) {
        assert block != null;
        assert block.length == RecoverableStream.META_BLOCK_SIZE;
        this.block = block.clone();
        assert pos >= 0;
        this.pos = pos;
    }
    
    public void setFromOtherMetaBlock(MetaBlock source) {
        if (source == null) {
            throw new IllegalArgumentException("source == null not allowed");
        }
        
        if (source.block == null || source.block.length != RecoverableStream.META_BLOCK_SIZE) {
            throw new IllegalArgumentException("bad source");
        }
        
        block = new byte[RecoverableStream.META_BLOCK_SIZE];
        System.arraycopy(source.block, 0, block, 0, source.block.length);
        this.pos = source.pos;
    }
    

    /**
     * If last byte is OK, this method can be used to check that the block bytes
     * follows the allowed meta block db stream format.
     * 
     * @throws StreamFormatException  If invalid byte format detected.
     */
    public void checkFormat() {
        //
        // Version is not checked here, it should have been checked already.
        //
        
        if (!isValid(block)) {
            return;
        }
        
        checkMagic();
        
        long last = getLastTransSpos();
        if (last < 0 && last != Constants.SposNULL) {
            throw new StreamFormatException("Meta block, bad last transaction spos: " + last + ".");
        }

        long time = this.getTime();
        if (time < 0) {
            throw new StreamFormatException("Meta block, bad time, " + time + ".");
        }
    }

    private void checkMagic() {
        for (int i = 0; i < 4; i++) {
            if (block[i] != MAGIC[i]) {
                throw new StreamFormatException("Illegal first bytes of block, offset=" + i 
                        + ", value=" + ((int) block[i]) + ".");
            }
        }
    }
    
    /**
     * Returns the stream position of this meta block, or -1 if unknown or not applicable.
     */
    final long getPos() {
        return pos;
    }
    
    /**
     * Returns a reference to the byte array block.
     */
    final byte[] getBlock() {
        return block;
    }
    
    /**
     * Returns the version of the stream format.
     */
    public int getVersion() {
        return Bytes.bytesToIntLE(block, 4);
    }
    
    public void setTime(long time) {
        Bytes.longToBytesLE(time, block, 8);
    }
    
    /**
     * Database time in db time units (100 ns units since Unix Epoch).
     */
    public long getTime() {
        return Bytes.bytesToLongLE(block, 8);
    }
    
    public void setId(byte[] id) {
        if (id == null) {
            throw new IllegalArgumentException("id == null not allowed");
        }
        
        if (id.length != 16) {
            throw new IllegalArgumentException("id.length is bad, " + id.length);
        }
        
        System.arraycopy(id, 0, this.block, 24, id.length);
    }
    
    public byte[] getId() {
        byte[] id = new byte[16];
        System.arraycopy(block, 24, id, 0, id.length);
        return id;
    }
    
    /**
     * Returns the spos of the last completed and valid transaction written to the stream
     * before the meta block was written.
     * Returns Constants.SposNULL if no transaction has been written to the 
     * stream before the meta block.
     */
    public long getLastTransSpos() {
        return Bytes.bytesToLongLE(block, 16);
    }
    
    /**
     * Sets the spos of the last completed and valid transaction written to the stream.
     * Use Constants.SposNULL if no transaction has run yet.
     */
    public void setLastTransSpos(long spos) {
        Bytes.longToBytesLE(spos, block, 16);
    }
    
    /**
     * The maximum node size of the database, from its creation (2026-10-27, bergdb 005-50).
     * A start refuses another size, and 0, which no block of version 155 has
     * (Db.refuseOtherNodeSize).
     */
    public int getMaxNodeSize() {
        return Bytes.bytesToUShortLE(block, 44);
    }
    
    /**
     * @throws IllegalArgumentException  if 'maxNodeSize' does not fit in an unsigned short
     */
    public void setMaxNodeSize(int maxNodeSize) {
        Bytes.ushortToBytesLE(maxNodeSize, block, 44);
    }
    
    /**
     * Returns true if the last byte is META_BLOCK_LAST_BYTE.
     */
    public boolean isValid() {
        return block[RecoverableStream.META_BLOCK_SIZE - 1] == META_BLOCK_LAST_BYTE;
    }
    
    /**
     * Returns true if metaBlockBytes == RecoverableStream.META_BLOCK_SIZE
     * and last byte is META_BLOCK_LAST_BYTE.
     * 
     * @param metaBlockBytes
     */
    public static boolean isValid(byte[] metaBlockBytes) {
        assert metaBlockBytes != null : "metaBlockBytes == null not allowed";
        return metaBlockBytes.length == RecoverableStream.META_BLOCK_SIZE 
                && metaBlockBytes[metaBlockBytes.length - 1] == META_BLOCK_LAST_BYTE;
    }
    
    /**
     * Whether 'bytes' begin as a meta block of this version, as far as they go: the magic
     * bytes, then the version, as readMetaBlock() reads them (2026-10-25, bergdb 005-33).
     * For a stream that a crash has cut in its first meta block.
     */
    static boolean beginsAsBlock(byte[] bytes) {
        final int n = Math.min(bytes.length, 4 + 4);    // FILL_OUT_TEMPLATE begins with them.
        for (int i = 0; i < n; i++) {
            if (bytes[i] != FILL_OUT_TEMPLATE[i]) {
                return false;
            }
        }
        return true;
    }
    
    /**
     * Unit tests for this class.
     */
    public static class Tester {
        private Tester() {}
                
        @Nano
        public static void time() {
            MetaBlock b = new MetaBlock();
            b.setTime(1234567);
            
            long time = b.getTime();
            Assert.assertEquals(1234567, time);
        }
        
        @Nano
        public static void version() {
            MetaBlock b = new MetaBlock();
            Assert.assertEquals(155, b.getVersion());
        }
        
        /** Bergdb 028-15: bytes 40 to 43, the startup distance until version 155, zero. */
        @Nano
        public static void startupDistanceBytesZero() {
            MetaBlock b = new MetaBlock();
            b.setMaxNodeSize(30);
            b.setLastTransSpos(1234);
            for (int i = 40; i < 44; i++) {
                Assert.assertEquals("byte " + i, 0, b.getBlock()[i]);
            }
        }
        
        /** Bergdb 005-50: the node size, 2 bytes at offset 44; 0 until it is set. */
        @Nano
        public static void maxNodeSize() {
            MetaBlock b = new MetaBlock();
            Assert.assertEquals(0, b.getMaxNodeSize());
            b.setMaxNodeSize(62);
            Assert.assertEquals(62, b.getMaxNodeSize());
            Assert.assertEquals(62, b.getBlock()[44]);
            for (int i = 45; i < RecoverableStream.META_BLOCK_SIZE - 1; i++) {
                Assert.assertEquals("byte " + i, 0, b.getBlock()[i]);
            }
            b.setMaxNodeSize(65535);
            Assert.assertEquals(65535, b.getMaxNodeSize());
        }
    }
}
