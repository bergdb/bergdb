package bergdb.pubimp;

import bergdb.common.Bug;
import bergdb.nanotest.Assert;
import bergdb.nanotest.T;
import bergdb.pub.BadFormatException;

/**
 * Class with static method for checking keys and converting them.
 * 
 * @author Frans Lundberg
 */
public class PubKeys {
    
    public static final char INTERNAL_DIR_PREFIX = '#';
    
    public static final char FILE_PREFIX = '-';
    
    public static final char DIR_PREFIX = 'd';
    
    /**
     * Converts a ukey to an ikey according to doc/2013-key-encoding.txt.
     * This method should always be applied to all keys as they cross the border between
     * the user application into the Pub Layer.
     * 
     * @param ukey The input ukey (user string key).
     * @return The ukey converted to an ikey.
     * @throws IllegalArgumentException  If ukey is null or invalid.
     */
    public static final String u2i(String ukey) throws IllegalArgumentException {
        // 130815, changed to throw IllegalArgumentException instead of BadFormatException.
        
        if (ukey == null) {
            throw new IllegalArgumentException("null is not a valid key.");
        }
        
        if (ukey.length() == 0) {
            throw new IllegalArgumentException("The empty string is not a valid key.");
        }
        
        if (ukey.charAt(0) != '/') {
            throw new IllegalArgumentException("Key does not start with mandatory '/', key: " + ukey);
        }
        
        if (ukey.length() < 2) { 
            throw new IllegalArgumentException("Key is too short: " + ukey);
        }
        
        StringBuilder b = new StringBuilder();
        
        int lastSlashIndex = ukey.lastIndexOf('/');
        if (lastSlashIndex == -1) {
            throw new Bug("Cannot happen, ukey: " + ukey);
        }
        
        int length = ukey.length();
        
        if (lastSlashIndex == length - 1) {
            throw new IllegalArgumentException("Key is not allowed to end with a '/', was: " + ukey);
        }
        
        int slashIndex = Integer.MIN_VALUE;
        
        for (int i = 0; i < length; i++) {
            char c = ukey.charAt(i);
            
            if (c == '/') {
                if (slashIndex == i - 1) {
                    throw new IllegalArgumentException("ukey cannot contain \"//\", was: " + ukey);
                }
                slashIndex = i;
                b.append(c);
                b.append(slashIndex == lastSlashIndex ? FILE_PREFIX : DIR_PREFIX);
            } else {
                b.append(c);
            }
        }
        
        String ikey = b.toString();
        return ikey;
    }
    
    
    /**
     * Converts a ukey directory to an ikey directory according to doc/2013-key-encoding.txt.
     */
    public static final String udir2idir(String udir) throws BadFormatException {
        
        // TODO X LATER Consider throwing IllegalArgumentException or subclass of it.
        
        if (udir == null) {
            throw new BadFormatException("null is not a valid dir.");
        }
        
        if (udir.length() == 0) {
            throw new BadFormatException("The empty string is not a valid dir.");
        }
        
        int length = udir.length();
        
        if (udir.charAt(length - 1) != '/') {
            throw new BadFormatException("udir must end with '/', was: " + udir);
        }
        
        StringBuilder b = new StringBuilder();
        
        int slashIndex = Integer.MIN_VALUE;
        
        for (int i = 0; i < length - 1; i++) {
            char c = udir.charAt(i);
            
            if (c == '/') {
                if (slashIndex == i - 1) {
                    throw new BadFormatException("udir cannot contain \"//\", was: " + udir);
                }
                slashIndex = i;
                b.append('/');
                b.append(DIR_PREFIX);
            } else {
                b.append(c);
            }
        }
        
        b.append(udir.charAt(length - 1));     // last char is a '/' - no added 'd' wanted.
        
        String idir = b.toString();
        return idir;
    }
    
    /**
     * Converts an ikey that was created from a ukey, back to the original ukey.
     * 
     * @throws IllegalArgumentException if ikey is not or not a valid ikey created from a ukey.
     */
    public static String i2u(String ikey) {
        if (ikey == null) {
            throw new IllegalArgumentException("ikey == null not allowed");
        }
        
        int length = ikey.length();
        
        if (length < 2) {
            throw new IllegalArgumentException("invalid ikey, too short, was: " + ikey);
        }
        
        if (ikey.charAt(0) != '/') {
            throw new IllegalArgumentException("an ikey should start with '/'");
        }
        
        StringBuilder b = new StringBuilder();
        boolean gotSlash = false;
        
        for (int i = 0; i < length; i++) {
            char c = ikey.charAt(i);
            if (gotSlash) {
                if (c == DIR_PREFIX || c == FILE_PREFIX) {
                    // fine :-)
                    gotSlash = false;
                } else {
                    throw new IllegalArgumentException("ikey cannot be converted to valid ukey, ikey: " + ikey);
                }
            } else {
                gotSlash = c == '/';
                b.append(c);
            }
        }
        
        String ukey = b.toString();
        return ukey;
    }
    
    @T
    public static void testToIkey0() {
        String ukey = "/db1/customers/c001.obj";
        String expected = "/ddb1/dcustomers/-c001.obj";
        Assert.assertEquals(expected, PubKeys.u2i(ukey));
    }
    
    private static char ARABIC_LETTER_JEEM = '\u062c';
    
    @T
    public static void testToIkey1() {
        String[] ukeys = new String[] {
                "/a",
                "/dir/Special Chars: \u0000\u0001\u0002",
                "/ÅÄÖ-" + ARABIC_LETTER_JEEM + "/\u0000.txt"
        };
        
        String[] expected = new String[] {
                "/-a",
                "/ddir/-Special Chars: \u0000\u0001\u0002",
                "/dÅÄÖ-" + ARABIC_LETTER_JEEM + "/-\u0000.txt"
        };
        
        for (int i = 0; i < ukeys.length; i++) {
            Assert.assertEquals(expected[i], PubKeys.u2i(ukeys[i]));
        }
    }
    
    private static void assertI2uException(String ukey) {
        Exception ex = null;
        
        try {
            u2i(ukey);
        } catch (IllegalArgumentException e) {
            ex = e;
        }
        
        Assert.assertTrue(ex != null);
    }
    
    @T
    public static void testToIkey2() {
        assertI2uException("");
        assertI2uException(null);
        assertI2uException("/dir/dir2//double-slash/not-allowed.txt");
        assertI2uException("/slash at end not allowed/");
    }
}
