package kissdb.test.java;

import java.io.ByteArrayOutputStream;
import java.io.DataOutputStream;

import kissdb.nanotest.TestCollector;
import kissdb.nanotest.T;

/**
 * Tests performance of data objects that stores whole string for type 
 * and field names compared to data object that would store type ID and 
 * field ID instead of full strings.
 * The example is a small class that keeps the balance of a monetary account.
 * 
 * @author Frans Lundberg
 */
public class ZipObject {
    @T("perf")
    public static void run(TestCollector r) throws Exception {
        ByteArrayOutputStream vout = new ByteArrayOutputStream();
        ByteArrayOutputStream cout = new ByteArrayOutputStream();
        DataOutputStream verboseOut;
        DataOutputStream compactOut;
        
        verboseOut = new DataOutputStream(vout);
        compactOut = new DataOutputStream(cout);
        
        for (int i=0; i<1000; i++) {
            verboseOut.writeUTF("com.skycash.data.Account");
            verboseOut.writeUTF("balance");
            verboseOut.writeLong(100000 + i*123456);
            verboseOut.writeUTF("currency");
            verboseOut.writeUTF("SEK");
            verboseOut.writeUTF("payCount");
            verboseOut.writeInt(i);
            
            compactOut.writeInt(34);
            compactOut.writeShort(0);
            compactOut.writeLong(100000 + i*123456);
            compactOut.writeShort(1);
            compactOut.writeUTF("SEK");
            compactOut.writeShort(0);
            verboseOut.writeInt(i);
        }
        
        verboseOut.close();
        compactOut.close();
        
        byte[] vbytes = vout.toByteArray();
        byte[] cbytes = cout.toByteArray();
        byte[] vbytes2 = Zip.deflate(vbytes, 7);
        byte[] cbytes2 = Zip.deflate(cbytes, 7);
        r.report("verboseBeforeSize", vbytes.length);
        r.report("compactBeforeSize", cbytes.length);
        r.report("verboseAfterSize", vbytes2.length);
        r.report("compactAfterSize", cbytes2.length);
        r.report("verboseCompression", 
                ((double) vbytes2.length)/vbytes.length);
        r.report("compactCompression", 
                ((double) cbytes2.length)/cbytes.length);
        r.report("compressedOverhead", 
                ((double) vbytes2.length)/cbytes2.length);
        r.report("uncompressedOverhead", 
                ((double) vbytes.length)/cbytes.length);
    }
}
