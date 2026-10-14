package bergdb.test.java;

import java.io.IOException;
import java.security.InvalidAlgorithmParameterException;
import java.security.InvalidKeyException;
import java.security.MessageDigest;
import java.security.NoSuchAlgorithmException;
import java.security.NoSuchProviderException;

//import java.security.Security;
import javax.crypto.NoSuchPaddingException;

import bergdb.nanotest.Nano;
import bergdb.nanotest.TestEnvironment;

//import org.bouncycastle.jce.provider.BouncyCastleProvider;

/**
 * Performance of computing a secure hash for SHA1, SHA256 och 
 * others.
 */
public class SecureHash {
    //static {
    //    Security.addProvider(new BouncyCastleProvider());
    //}
    
    @Nano("perf")
    public static void run(TestEnvironment c) throws Exception {
        String[] names = {
                //"Tiger",
                "SHA1",
                "SHA256",
                "MD5",
                //"RipeMD128",
                //"RipeMD256"
        };
        
        String[] providers = {
                //"BC",
                null,
                null,
                null,
                //"BC",
                //"BC"
        };
        
        for (int i = 0; i < names.length; i++) {
            hashPerf(c, names[i], providers[i]);
        }
    }
    
    private static void hashPerf(TestEnvironment c, String name, String provider) 
            throws NoSuchPaddingException,
            NoSuchAlgorithmException, IOException, NoSuchProviderException,
            InvalidKeyException, InvalidAlgorithmParameterException {
        MessageDigest digest;
        
        long t0;
        int n = 0;
        byte[] testData = new byte[1024 * 1024];
        
        if (provider == null) {
            digest = MessageDigest.getInstance(name);
        } else {
            digest = MessageDigest.getInstance(name, provider);
        }
        
        t0 = System.nanoTime();
        while (true) {
            digest.update(testData);
            if (System.nanoTime() - t0 > 1e9) {
                break;
            }
        }
        
        n = 0;
        long bytesWritten = 0;
        t0 = System.nanoTime();
        while (true) {
            digest.update(testData);
            bytesWritten += testData.length;
            n++;
            if (System.nanoTime() - t0 > 1e9) {
                break;
            }
        }
        double time = (System.nanoTime() - t0) * 1e-9;
        
        c.report(name, n/time);
        c.report("bytesWritten", bytesWritten);
    }
}
