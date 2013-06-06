package kissdb.test.java;

import java.io.IOException;
import java.security.InvalidAlgorithmParameterException;
import java.security.InvalidKeyException;
import java.security.NoSuchAlgorithmException;
import java.security.NoSuchProviderException;
//import java.security.Security;

import javax.crypto.Mac;
import javax.crypto.NoSuchPaddingException;
import javax.crypto.spec.SecretKeySpec;

import kissdb.nanotest.TestCollector;
import kissdb.nanotest.T;


//import org.bouncycastle.jce.provider.BouncyCastleProvider;

/**
 * Performance of message authentication code algorithms.
 */
public class MacPerf {
    //static {
    //    Security.addProvider(new BouncyCastleProvider());
    //}
    
    @T("perf")
    public static void run(TestCollector c) throws Exception {
        String[] names = {
                "HmacMD5",
                "HmacSHA1",
                "HmacSHA256",
                //"Hmac-RipeMD128",
                //"Hmac-RipeMD160"
        };
        
        String[] providers = {
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
    
    private static void hashPerf(TestCollector c, String name, String provider) 
            throws NoSuchPaddingException,
            NoSuchAlgorithmException, IOException, NoSuchProviderException,
            InvalidKeyException, InvalidAlgorithmParameterException {
        Mac mac;
        
        long t0;
        byte[] testData = new byte[1024 * 1024];
        
        if (provider == null) {
            mac = Mac.getInstance(name);
        } else {
            mac = Mac.getInstance(name, provider);
        }
        
        byte[] key = new byte[16];
        SecretKeySpec keySpec = new SecretKeySpec(key, "AES");
        
        mac.init(keySpec);
        
        t0 = System.nanoTime();
        while (true) {
            mac.update(testData);
            if (System.nanoTime() - t0 > 1e9) {
                break;
            }
        }
        
        long bytesWritten = 0;
        t0 = System.nanoTime();
        while (true) {
            mac.update(testData);
            bytesWritten += testData.length;
            if (System.nanoTime() - t0 > 1e9) {
                break;
            }
        }
        double time = (System.nanoTime() - t0) * 1e-9;
        
        c.report(name, bytesWritten / (1024*1024) / time);
    }
}
