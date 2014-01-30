package bergdb.test.java;

import java.io.ByteArrayInputStream;
import java.io.ByteArrayOutputStream;
import java.io.DataOutputStream;
import java.io.IOException;
import java.io.InputStream;
import java.io.OutputStream;
import java.util.Random;
import java.util.zip.Deflater;
import java.util.zip.DeflaterOutputStream;
import java.util.zip.InflaterInputStream;

import bergdb.nanotest.T;
import bergdb.nanotest.TestCollector;

/**
 * ZIP performance, compression of random longs.
 * 
 * @author Frans Lundberg
 */
public class Zip {
    private double time;
    private int N = 100000;
    private TestCollector r;
    private int compressionLevel = 7;
    
    public long[] createInts(int n) {
        Random random = new Random(0);
        long[] ints = new long[n];
        for (int i = 0; i < n; i++) {
            ints[i] = random.nextLong();
        }
        return ints;
    }
    
    private byte[] timedDeflate(byte[] bytes) {
        double t1, t0;
        byte[] bytesOut;
        
        t0 = System.nanoTime();
        bytesOut = deflate(bytes, this.compressionLevel);
        t1 = System.nanoTime();
        time = (t1 - t0) / 1e9;
        
        return bytesOut;
    }
    
    public static byte[] deflate(byte[] bytes, int level) {
        Deflater d = new Deflater();
        d.setLevel(level);
        ByteArrayOutputStream bout = new ByteArrayOutputStream();
        DeflaterOutputStream out = new DeflaterOutputStream(bout, d);
        
        try {
            out.write(bytes);
            out.close();
        } catch (IOException e) {
            throw new Error(e);
        }
        
        return bout.toByteArray();
    }
    
    private void overhead() {
        double t0, t1;
        byte[] in = new byte[]{1};
        int count = 100;
        
        t0 = System.nanoTime();
        for (int i = 0; i < count; i++) {
            timedDeflate(in);
        }
        t1 = System.nanoTime();
        
        r.report("deflateOverheadTime", (t1-t0)/1.0e9 / count);
    }
    
    private byte[] inflate(byte[] bytes) {
        double t0, t1;
        ByteArrayInputStream bin = new ByteArrayInputStream(bytes);
        InflaterInputStream in = new InflaterInputStream(bin);
        ByteArrayOutputStream bout = new ByteArrayOutputStream();
        
        try {
            t0 = System.nanoTime();
            copy(in, bout);
            t1 = System.nanoTime();
            time = (t1 - t0) / 1e9;
        } catch (IOException e) {
            throw new Error(e);
        }
        return bout.toByteArray();
    }
    
    private void copy(InputStream in, OutputStream out) throws IOException {
        byte[] buffer = new byte[1024];
        int count;
        
        while (true) {
            count = in.read(buffer);
            if (count == -1) {
                break;
            } else {
                out.write(buffer, 0, count);
            }
        }
    }

    @T("perf")
    public static void run(TestCollector c) throws Exception {
        Zip z = new Zip();
        long[] ints = new long[z.N];
        StringBuilder b = new StringBuilder();
        int stringCompressedSize;
        
        z.r = c;
        ints = z.createInts(z.N);
        
        z.overhead();
        c.report("compressionLevel", z.compressionLevel);
        
        // Compression of string data
        
        for (int i = 0; i < z.N; i++) {
            b.append(ints[i]);
            if (i != z.N - 1) {
                b.append(',');
            }
        }
        
        byte[] in;
        byte[] out;
        in = b.toString().getBytes("UTF-8");
        out = z.timedDeflate(in);
        stringCompressedSize = out.length;
        
        c.report("stringCompression", 
                ((double) out.length) / in.length);
        c.report("stringDeflateTimePerInByte", z.time/in.length);
        c.report("stringDeflateTimePerOutByte", z.time/out.length);
        
        in = z.inflate(out);
        c.report("stringInflateTimePerInByte", z.time/out.length);
        c.report("stringInflateTimePerOutByte", z.time/in.length);
        
        // Compression of binary data
        
        ByteArrayOutputStream binary = new ByteArrayOutputStream();
        DataOutputStream dout = new DataOutputStream(binary);
        int binaryCompressedSize;
        
        for (int i = 0; i < z.N; i++) {
            dout.writeLong(ints[i]);
        }
        dout.close();
        in = binary.toByteArray();
        out = z.timedDeflate(in);
        binaryCompressedSize = out.length;
        
        c.report("binaryCompression", 
                ((double) out.length) / in.length);
        c.report("binaryDeflateTimePerInByte", z.time/in.length);
        c.report("binaryDeflateTimePerOutByte", z.time/out.length);
        c.report("stringSizeOverhead", 
                ((double) stringCompressedSize) / binaryCompressedSize);
        
        z.compressedLongs();
    }
    
    /**
     * Compression of binary longs compared to bytes.
     * What's the storage overhead of using a long instead of a shorter
     * integer type?
     */
    private void compressedLongs() {
        long[] longs1 = new long[10000];
        long[] longs2 = new long[10000];
        Random random = new Random(0);
        ByteArrayOutputStream bout1 = new ByteArrayOutputStream();
        DataOutputStream dout1 = new DataOutputStream(bout1);
        ByteArrayOutputStream bout2 = new ByteArrayOutputStream();
        DataOutputStream dout2 = new DataOutputStream(bout2);
        
        for (int i = 0; i < longs1.length; i++) {
            longs1[i] = (long) (random.nextDouble() * 16.0);   // overhead 0.87
            //longs1[i] = (long) (random.nextDouble() * 64.0);   // overhead 1.27
            //longs1[i] = (long) (random.nextDouble() * 256.0);  // overhead 1.68
            
            //longs2[i] = (long) (random.nextDouble() * 256.0*1.0);  // overhead 0.84
            //longs2[i] = (long) (random.nextDouble() * 256.0*16.0);  // overhead 1.14
            //longs2[i] = (long) (random.nextDouble() * 256.0*256.0);  // overhead 1.44
            
            //longs2[i] = (long) (random.nextDouble() * 256.0*256.0*256.0*256.0);
            
            try {
                dout1.writeLong(longs1[i]);
                dout2.writeLong(longs2[i]);
            } catch (IOException e) {
                throw new Error(e);
            }
        }
        
        try {
            dout1.close();
            dout2.close();
        } catch (IOException e) {
            throw new Error(e);
        }
        
        byte[] compressed = deflate(bout1.toByteArray(), 7);
        r.report("longOverheadComparedToBytes", 
                (double) compressed.length / longs1.length);
        
        compressed = deflate(bout2.toByteArray(), 9);
        r.report("longOverheadComparedToShorts", 
                (double) compressed.length / (2.0 * longs2.length));
    }
}

/*
NOTES 080816

There is no large overhead of storing integer values using longs instead
of smaller integer types (int, short, byte) if the data is going to be 
compressed anyway.
For random data that would fit a byte, the overhead of storing in a long is 1.68.
For random data that would fit a short, the overhead is 1.44.
For random data that would fit an int, the overhead is 1.26.
This is at DEFLATE compression level 7 (out of range 1-9).

081102

$ java -cp source/bin/bergdb.jar com.bergdb.perf.Starter 
com.bergdb.perf.Zip.deflateOverhead = 0.0043886771
com.bergdb.perf.Zip.compressionLevel = 7
com.bergdb.perf.Zip.stringCompression = 0.48188013533582186
com.bergdb.perf.Zip.stringDeflateTimePerInByte = 2.2562914519939654E-7
com.bergdb.perf.Zip.stringDeflateTimePerOutByte = 4.6822669924369423E-7
com.bergdb.perf.Zip.stringInflateTimePerInByte = 8.823748673460449E-8
com.bergdb.perf.Zip.stringInflateTimePerOutByte = 4.2519892049364E-8
com.bergdb.perf.Zip.binaryCompression = 1.00031375
com.bergdb.perf.Zip.binaryDeflateTimePerInByte = 1.2365136625E-7
com.bergdb.perf.Zip.binaryDeflateTimePerOutByte = 1.2361258280214584E-7
com.bergdb.perf.Zip.stringSizeOverhead = 1.2269625405029172
com.bergdb.perf.Zip.longOverheadComparedToBytes = 0.8676
com.bergdb.perf.Zip.longOverheadComparedToShorts = 0.0050
com.bergdb.perf.ZipDeltaInts.deflateOverhead = 2.1575245E-4
com.bergdb.perf.ZipDeltaInts.compressionLevel = 7
com.bergdb.perf.ZipDeltaInts.stringCompression = 0.1254519645009355
com.bergdb.perf.ZipDeltaInts.stringDeflateTimePerInByte = 7.792454139263875E-8
com.bergdb.perf.ZipDeltaInts.stringDeflateTimePerOutByte = 6.211504275969921E-7
com.bergdb.perf.ZipDeltaInts.stringInflateTimePerInByte = 2.4377930832912636E-7
com.bergdb.perf.ZipDeltaInts.stringInflateTimePerOutByte = 3.058259313456816E-8
com.bergdb.perf.ZipDeltaInts.binaryCompression = 0.33902
com.bergdb.perf.ZipDeltaInts.binaryDeflateTimePerInByte = 4.0897915875000005E-7
com.bergdb.perf.ZipDeltaInts.binaryDeflateTimePerOutByte = 1.2063570253967319E-6
com.bergdb.perf.ZipDeltaInts.stringSizeOverhead = 0.9713623090083181
com.bergdb.perf.ZipDeltaInts.longOverheadComparedToBytes = 0.8676
com.bergdb.perf.ZipDeltaInts.longOverheadComparedToShorts = 0.0050
com.bergdb.perf.ZipObject.verboseBeforeSize = 76000
com.bergdb.perf.ZipObject.compactBeforeSize = 23000
com.bergdb.perf.ZipObject.verboseAfterSize = 7393
com.bergdb.perf.ZipObject.compactAfterSize = 3486
com.bergdb.perf.ZipObject.verboseCompression = 0.09727631578947368
com.bergdb.perf.ZipObject.compactCompression = 0.15156521739130435
com.bergdb.perf.ZipObject.compressedOverhead = 2.1207687894434883
com.bergdb.perf.ZipObject.uncompressedOverhead = 3.3043478260869565
*/