package bergdb.common;

import java.util.zip.CRC32;
import java.util.zip.Checksum;
import bergdb.nanotest.Assert;
import bergdb.nanotest.Nano;

/**
 * An enhanced Checksum implementation that can be 
 * updated based on other values types (long, boolean) than byte values.
 * 
 * @author Frans Lundberg
 */
public class MyChecksum implements Checksum {
    private final Checksum wrapped;
    
    public MyChecksum(Checksum wrapped) {
        this.wrapped = wrapped;
    }
    
    public void update(int b) {
        wrapped.update(b);
    }
    
    /**
     * Updates checksum with a long value.
     */
    public void updateWithLong(long value) {
        byte[] buffer = new byte[8];
        Bytes.longToBytesLE(value, buffer, 0);
        wrapped.update(buffer, 0, 8);
    }
    
    public void updateWithBoolean(boolean value) {
        wrapped.update(value == true ? 1 : 0);
    }

    public void update(byte[] b, int off, int len) {
        wrapped.update(b, off, len);
    }

    public long getValue() {
        return wrapped.getValue();
    }

    public void reset() {
        wrapped.reset();
    }
    
    @Nano
    public static void test0() {
        Checksum sum1 = new CRC32();
        Checksum sum2 = new CRC32();
        MyChecksum my = new MyChecksum(sum2);
        
        sum1.update(1);
        my.updateWithBoolean(true);
        
        sum1.update(new byte[]{1, 2, 0, 0, 0, 0, 0, 0}, 0, 8);
        my.updateWithLong(1 + 2*256);
        
        Assert.assertEquals(sum1.getValue(), my.getValue());
    }
}
