package bergdb.test.java;

import java.io.IOException;
import java.security.InvalidAlgorithmParameterException;
import java.security.InvalidKeyException;
import java.security.NoSuchAlgorithmException;
import java.security.NoSuchProviderException;

import javax.crypto.Cipher;
import javax.crypto.CipherOutputStream;
import javax.crypto.NoSuchPaddingException;
import javax.crypto.spec.IvParameterSpec;
import javax.crypto.spec.SecretKeySpec;

import bergdb.common.NullOutputStream;
import bergdb.nanotest.T;
import bergdb.nanotest.TestCollector;

//import org.bouncycastle.jce.provider.BouncyCastleProvider;


public class Ciphers {
    //static {
    //    Security.addProvider(new BouncyCastleProvider());
    //}
    
    @T("perf")
    public static void run(TestCollector c) throws Exception {
        String[] cipherNames = {
                "AES/CBC/PKCS5Padding",
                "AES/OFB8/NoPadding",
                "AES/CFB8/NoPadding",
                "AES/OFB128/NoPadding",
                //"Salsa20",
                //"HC128"
        };
        
        String[] providers = {
                null,
                null,
                null,
                null,
                //"BC",
                //"BC"
        };
        
        c.out().println("Cipher speeds in MiB/s.");
        for (int i = 0; i < cipherNames.length; i++) {
            cipherPerf(c, cipherNames[i], providers[i]);
        }
    }
    
    private static void cipherPerf(TestCollector c, String cipherName, String provider) 
            throws NoSuchPaddingException,
            NoSuchAlgorithmException, IOException, NoSuchProviderException,
            InvalidKeyException, InvalidAlgorithmParameterException {
        Cipher cipher;
        long t0;
        byte[] testData = new byte[1024 * 128];
        
        if (provider == null) {
            cipher = Cipher.getInstance(cipherName);
        } else {
            cipher = Cipher.getInstance(cipherName, provider);
        }
        
        byte[] key = new byte[16];
        byte[] iv = new byte[16];
        SecretKeySpec keySpec = new SecretKeySpec(key, "AES");
        
        if (cipherName.contains("256")) {
            key = new byte[32];
            keySpec = new SecretKeySpec(key, "HC256");
        }
        
        if (cipherName.contains("Salsa")) {
            iv = new byte[8];
        }
        
        for (int i = 0; i < key.length; i++) {
            key[i] = (byte) i;
        }
        for (int i = 0; i < iv.length; i++) {
            iv[i] = (byte) i;
        }
        
        
        IvParameterSpec ivSpec = new IvParameterSpec(iv);
        
        try {
            cipher.init(Cipher.ENCRYPT_MODE, keySpec, ivSpec);
        } catch (InvalidKeyException e) {
            throw new Error(e);
        } catch (InvalidAlgorithmParameterException e) {
            throw new Error(e);
        }
        
        CipherOutputStream cout = new CipherOutputStream(
                new NullOutputStream(), cipher);
        
        t0 = System.nanoTime();
        while (true) {
            cout.write(testData);
            if (System.nanoTime() - t0 > 1e9) {
                break;
            }
        }
        
        long bytesWritten = 0;
        t0 = System.nanoTime();
        while (true) {
            cout.write(testData);
            bytesWritten += testData.length;
            if (System.nanoTime() - t0 > 1e9) {
                break;
            }
        }
        double time = (System.nanoTime() - t0) * 1e-9;
        cout.close();
        
        c.report(cipherName, bytesWritten / (time * 1024 * 1024));
        
        long count = 0;
        t0 = System.nanoTime();
        while (true) {
            cipher.init(Cipher.ENCRYPT_MODE, keySpec, ivSpec);
            count++;
            if (System.nanoTime() - t0 > 1e9) {
                break;
            }
        }
        time = (System.nanoTime() - t0) * 1e-9;
        
        c.report(cipherName + "-initTime", time/count);
    }
}

/*
Result on my laptop (Acer Extensa, 081025).

$ java -server -cp source/bin/bergdb.jar:source/bin/commons-collections-3.2.1.jar:../BergDB_storage/bc/bcprov-jdk16-141.jar com.bergdb.perf.Starter
Cipher speeds in MiB/s.
com.bergdb.perf.Ciphers.AES/CBC/PKCS5Padding = 23.99646184168375
com.bergdb.perf.Ciphers.AES/CBC/PKCS5Padding-initTime = 1.0306776859333774E-5
com.bergdb.perf.Ciphers.AES/OFB8/NoPadding = 1.872137995249694
com.bergdb.perf.Ciphers.AES/OFB8/NoPadding-initTime = 7.699674173827343E-6
com.bergdb.perf.Ciphers.AES/CFB8/NoPadding = 1.9027190658398296
com.bergdb.perf.Ciphers.AES/CFB8/NoPadding-initTime = 6.729778264727233E-6
com.bergdb.perf.Ciphers.AES/OFB128/NoPadding = 20.226431918811016
com.bergdb.perf.Ciphers.AES/OFB128/NoPadding-initTime = 6.558951595130654E-6
com.bergdb.perf.Ciphers.Salsa20 = 32.43852594411447
com.bergdb.perf.Ciphers.Salsa20-initTime = 1.6333851616886574E-6
com.bergdb.perf.Ciphers.HC128 = 45.56940670957251
com.bergdb.perf.Ciphers.HC128-initTime = 5.617454538815864E-5
com.bergdb.perf.MacPerf.HmacMD5 = 132.8870663253446
com.bergdb.perf.MacPerf.HmacSHA1 = 79.00580704137595
com.bergdb.perf.MacPerf.HmacSHA256 = 33.41872797959538
com.bergdb.perf.SecureHash.SHA1 = 79.16009931394395
com.bergdb.perf.SecureHash.SHA256 = 35.55935789574512
com.bergdb.perf.SecureHash.MD5 = 136.77045786702087
com.bergdb.perf.SecureHash.RipeMD128 = 66.72175021834269
com.bergdb.perf.SecureHash.RipeMD256 = 53.013973231625044
*/