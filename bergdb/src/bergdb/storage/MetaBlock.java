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
 * FORMAT OF A META BLOCK, v154
 * Offset  Size    Description
 * 0       4       Magic bytes, meta block signature. Always the bytes for ASCII "berg".
 * 4       4       Version of BergDB stream format as an int (154 for this version).
 * 8       8       time, database time as a long.
 * 16      8       lastTrans, spos of last valid transaction completely written
 *                 before the meta block.
 * 24     16       Database ID. 128 random bits, used as unique database ID.
 * 40      4       startupDistance in bytes. Typically 20M.
 * 44     83       Reserved, must be set to zero.
 * 127     1       META_BLOCK_LAST_BYTE. 1 is used to indicate that the block is valid.
 * </pre>
 */
public class MetaBlock {    
    private static final byte META_BLOCK_LAST_BYTE = (byte) Util.identity(10);
    private static final byte[] MAGIC = new byte[] {'b', 'e', 'r', 'g'};
    public static final int VERSION_133 = Util.identity(133);
    public static final int VERSION_154 = Util.identity(154);
    private static final int CURRENT_VERSION = VERSION_154;
    
    private byte[] block;
    private long pos;         // stream pos, only used sometimes
    
    /**
     * Creates a new MetaBlock with startPos = 0.
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
    
    public void setPos(long pos) {
        this.pos = pos;
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
        return Bytes.bytesToUShortLE(block, 4);
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
    
    public int getStartupDistance() {
        return Bytes.bytesToIntLE(block, 40);
    }
    
    public void setStartupDistance(int startupDistance) {
        Bytes.intToBytesLE(startupDistance, block, 40);
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
            Assert.assertEquals(154, b.getVersion());
        }
        
        @Nano
        public static void startupDistance() {
            MetaBlock b = new MetaBlock();
            b.setStartupDistance(10*1000000);
            Assert.assertEquals(10*1000000, b.getStartupDistance());
        }
    }
}
