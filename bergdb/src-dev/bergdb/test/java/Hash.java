package bergdb.test.java;

import java.io.UnsupportedEncodingException;
import java.security.MessageDigest;
import java.security.NoSuchAlgorithmException;
import java.util.HashMap;
import java.util.Random;

import bergdb.nanotest.T;
import bergdb.nanotest.TestEnvironment;


/**
 * Execution speed of hash functions including MD5, SHA1.
 * 
 * @author Frans Lundberg
 */
public class Hash {
    
    @T("perf")
    public static void secureHash(TestEnvironment c) throws NoSuchAlgorithmException, UnsupportedEncodingException {
        //MessageDigest d = MessageDigest.getInstance("MD5");
        MessageDigest d = MessageDigest.getInstance("SHA1");
        byte[] bytes1 = "R/Accounts/46700000000".getBytes("UTF-8");
        byte[] bytes2 = "R/Accounts/46700000000.balance".getBytes("UTF-8");
        long t0, t1;
        int N = 1000;
        
        t0 = System.nanoTime();
        for (int i = 0; i < N; i++) {
            d.digest(bytes1);
            d.digest(bytes2);
        }
        t1 = System.nanoTime();
        
        double time = 1e-9 * (t1 - t0);
        c.report("timePerMD5Digest", time / (2*N));
    }
    
    @T("perf")
    public static void stringHash(TestEnvironment c) {
        String s1 = "R/Accounts/46700000000";
        String s2 = "R/Accounts/46700000000.balance";
        long t0, t1;
        int N = 10000;
        
        t0 = System.nanoTime();
        for (int i = 0; i < N; i++) {
            s1.hashCode();
            s2.hashCode();
            s1.hashCode();
            s2.hashCode();
            s1.hashCode();
            s2.hashCode();
            s1.hashCode();
            s2.hashCode();
            s1.hashCode();
            s2.hashCode();
        }
        t1 = System.nanoTime();
        
        double time = 1e-9 * (t1 - t0);
        c.report("timePerStringHash", time / (10*N));
    }
    
    /**
     * How fast is hash map for possible BergDB memory blocks?
     */
    @T("perf")
    public static void hashMap(TestEnvironment c) {
        Random rand = new Random(0);
        rand.setSeed(0);
        byte[] block = new byte[4 * 1024];
        HashMap<Long, Object> map = new HashMap<Long, Object>(10*1000);
        for (int i = 0; i < 10000; i++) {
            map.put(rand.nextLong(), block);
        }
        
        long t0, t1;
        int N = 1000;
        rand.setSeed(0);
        
        t0 = System.nanoTime();
        for (int i = 0; i < N; i++) {
            map.get(rand.nextLong());
            map.get(rand.nextLong());
            map.get(rand.nextLong());
            map.get(rand.nextLong());
            map.get(rand.nextLong());
        }
        t1 = System.nanoTime();
        
        
        double time = 1e-9 * (t1 - t0);
        c.report("timePerHashMapLookup", time / (5*N));
    }
}

/*
080920, Frans, Acer Extensa laptop, Ubuntu, JVM 1.6 -server.
    MD5 digest takes 14 us.
    SHA1 digest takes 54 us.
    String.hashCode is 1000 times faster than SHA1: 53 ns.
    HashMap lookup using Longs as key takes 1.0 us on my laptop. Longer than
        expected! Specialized hashmap using long indexes would be faster.
*/
