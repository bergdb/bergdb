package bergdb.core;

import java.util.Iterator;
import java.util.Random;

import bergdb.common.Bytes;
import bergdb.common.Util;
import bergdb.graph.Keys;
import bergdb.nanotest.T;

/**
 * Sets of keys useful for testing the database.
 * 
 * @author Frans Lundberg
 */
public class KeyFactory {
    
    public static Iterable<String> shortRandomKeys(final int size) {
        return new Iterable<String>() {
            public Iterator<String> iterator() {
                return new Iterator<String>() {
                    int index = 0;
                    Random random = new Random(0);
                    
                    public boolean hasNext() {
                        return index < size;
                    }

                    public String next() {
                        String result = "k" + random.nextLong();
                        index++;
                        return result;
                    }

                    public void remove() {
                        throw new UnsupportedOperationException();
                    }
                };
            }
        };
    }
    
    /**
     * A key created with: "Util.toBytes("" + i);".
     */
    public static byte[] intKey(int i) {
        return Keys.toBytes("" + i);
    }
    
    /**
     * Returns a 4-byte key thay is the binary big-endian representation 
     * of 'i'.
     */
    public static byte[] binaryIntKey(int i) {
        byte[] bytes = new byte[4];
        Bytes.intToBytesBE(i, bytes, 0);
        return bytes;
    }
    
    /**
     * Returns a 4-byte key that is the binary little-endian representation 
     * of 'i'.
     */
    public static byte[] binaryIntKeyLE(int i) {
        byte[] bytes = new byte[4];
        Bytes.intToBytesLE(i, bytes, 0);
        return bytes;
    }
    
    private static String[] crazyPrefixes = new String[] {
        "r/customers/",
        "r/internal/admins/",
        "home/frasse/.eclipse/settings/",
        "home/frasse/notes/",
        "media/usb/music/mp3/bach/"
    };
    
    /**
     * Returns a "crazy" key. Lots of variation. Different keys for different
     * indexes is guaranteed. Different key lengths, string-based and binary-based ones.
     */
    public static byte[] crazyKey(int index) {
        if (index < 0) {
            throw new IllegalArgumentException("index < 0 not allowed " + index);
        }
        Random r = new Random(index);
        byte[] key;
        int type = r.nextInt(10);
        
        switch (type) {
        case 0:
        case 1:
        case 2:
            // Case 'B' - binary.
            key = new byte[5];
            key[key.length - 1] = (byte) 'B';
            Bytes.intToBytesLE(index, key, 0);
            break;
        case 3:
        case 4:
        case 5:
            // Case 'I'.
            key = Util.toBytes(index + "I");
            break;
        case 6:
            // Case 'L' - a longer key
            int size = r.nextInt(1000) + 20;
            if (r.nextDouble() < 0.02) {
                // Very long key
                size = r.nextInt(10*1000) + 20;
            }
            
            key = new byte[size];
            key[key.length - 1] = (byte) 'L';
            int myInt = Math.abs(r.nextInt(1000*1000)) + 10000;
            Bytes.stringToBytes("" + myInt, key, 0);
            Bytes.intToBytesBE(index, key, key.length - 5);
            break;
        case 7:
            // Case 'P'.
            // String key, long same-prefix for many keys.
            String s = "r/examples/A long directory name/followed by another one/" + index + "-P";
            key = Keys.toBytes(s);
            break;
        case 8:
        case 9:
            // Case 'C'.
            int i = r.nextInt(crazyPrefixes.length);
            key = Keys.toBytes(crazyPrefixes[i] + index + "-C");
            break;
        default:
            throw new Error();
        }
        
        return key;
    }
    
    /**
     * Returns a "crazy" key, all strings. Lots of variation. Different keys for different
     * indexes is guaranteed. Varying key lengths.
     * Similar to crazyKey(), but without binary keys.
     */
    public static byte[] crazyStringKey(int index) {
        if (index < 0) {
            throw new IllegalArgumentException("index < 0 not allowed " + index);
        }
        Random r = new Random(index);
        byte[] key;
        int type = r.nextInt(10);
        
        switch (type) {
        case 0:
        case 1:
        case 2:
            // Case 'B'
            StringBuilder b = new StringBuilder("" + (1*1000000 + index));
            int len = b.length();
            int stop = len / 2;
            
            // Reversing order of chars
            for (int i = 0; i < stop; i++) {
                char c = b.charAt(i);
                b.setCharAt(i, b.charAt(len - 1 - i));
                b.setCharAt(len - 1- i, c);
            }
            b.append("B");
            key = Keys.toBytes(b.toString());
            break;
        case 3:
        case 4:
        case 5:
            // Case 'I'.
            key = Keys.toBytes(index + "I");
            break;
        case 6:
            // Case 'L' - a longer key
            int size = r.nextInt(1000) + 20;
            if (r.nextDouble() < 0.02) {
                // Very long key
                size = r.nextInt(10*1000) + 20;
            }
            
            key = new byte[size];
            key[key.length - 1] = (byte) 'L';
            int myInt = Math.abs(r.nextInt(1000*1000)) + 10000;
            Bytes.stringToBytes("" + myInt, key, 0);
            Bytes.intToBytesBE(index, key, key.length - 5);
            break;
        case 7:
            // Case 'P'.
            // String key, long same-prefix for many keys.
            String s = "r/examples/A long directory name/followed by another one/" + index + "-P";
            key = Keys.toBytes(s);
            break;
        case 8:
        case 9:
            // Case 'C'.
            int i = r.nextInt(crazyPrefixes.length);
            key = Keys.toBytes(crazyPrefixes[i] + index + "-C");
            break;
        default:
            throw new Error();
        }
        
        return key;
    }
    
    @T
    public static void testGettingCrazy() {
        for (int i = 0; i < 1000; i++) {
            KeyFactory.crazyKey(i);
        }
    }
}
